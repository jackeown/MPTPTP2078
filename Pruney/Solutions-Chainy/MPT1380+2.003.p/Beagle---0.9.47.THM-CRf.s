%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:06 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 145 expanded)
%              Number of leaves         :   26 (  63 expanded)
%              Depth                    :   16
%              Number of atoms          :  124 ( 443 expanded)
%              Number of equality atoms :   20 (  52 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v4_pre_topc > v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( ( v3_pre_topc(B,A)
                    & r2_hidden(C,B) )
                 => m1_connsp_2(B,A,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v3_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_tops_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_82,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> r2_hidden(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

tff(c_18,plain,(
    ~ m1_connsp_2('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_20,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_30,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_34,plain,(
    ! [A_26,B_27] :
      ( k3_subset_1(A_26,k3_subset_1(A_26,B_27)) = B_27
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_40,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_26,c_34])).

tff(c_22,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_11),B_12),A_11)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ v3_pre_topc(B_12,A_11)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k3_subset_1(A_1,B_2),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_125,plain,(
    ! [A_36,B_37] :
      ( k3_subset_1(u1_struct_0(A_36),k2_pre_topc(A_36,k3_subset_1(u1_struct_0(A_36),B_37))) = k1_tops_1(A_36,B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_153,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_125])).

tff(c_157,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_153])).

tff(c_158,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_157])).

tff(c_161,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_2,c_158])).

tff(c_165,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_161])).

tff(c_167,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_157])).

tff(c_6,plain,(
    ! [B_7,A_5] :
      ( v4_pre_topc(B_7,A_5)
      | k2_pre_topc(A_5,B_7) != B_7
      | ~ v2_pre_topc(A_5)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_170,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) != k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_167,c_6])).

tff(c_178,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) != k3_subset_1(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_170])).

tff(c_206,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) != k3_subset_1(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_8,plain,(
    ! [A_5,B_7] :
      ( k2_pre_topc(A_5,B_7) = B_7
      | ~ v4_pre_topc(B_7,A_5)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_173,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_167,c_8])).

tff(c_181,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_173])).

tff(c_207,plain,(
    ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_206,c_181])).

tff(c_210,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_207])).

tff(c_214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_22,c_26,c_210])).

tff(c_216,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_10,plain,(
    ! [A_8,B_10] :
      ( k3_subset_1(u1_struct_0(A_8),k2_pre_topc(A_8,k3_subset_1(u1_struct_0(A_8),B_10))) = k1_tops_1(A_8,B_10)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_221,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_10])).

tff(c_225,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_40,c_221])).

tff(c_14,plain,(
    ! [C_19,A_13,B_17] :
      ( m1_connsp_2(C_19,A_13,B_17)
      | ~ r2_hidden(B_17,k1_tops_1(A_13,C_19))
      | ~ m1_subset_1(C_19,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ m1_subset_1(B_17,u1_struct_0(A_13))
      | ~ l1_pre_topc(A_13)
      | ~ v2_pre_topc(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_229,plain,(
    ! [B_17] :
      ( m1_connsp_2('#skF_2','#skF_1',B_17)
      | ~ r2_hidden(B_17,'#skF_2')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_17,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_14])).

tff(c_233,plain,(
    ! [B_17] :
      ( m1_connsp_2('#skF_2','#skF_1',B_17)
      | ~ r2_hidden(B_17,'#skF_2')
      | ~ m1_subset_1(B_17,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_229])).

tff(c_236,plain,(
    ! [B_41] :
      ( m1_connsp_2('#skF_2','#skF_1',B_41)
      | ~ r2_hidden(B_41,'#skF_2')
      | ~ m1_subset_1(B_41,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_233])).

tff(c_239,plain,
    ( m1_connsp_2('#skF_2','#skF_1','#skF_3')
    | ~ r2_hidden('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_236])).

tff(c_242,plain,(
    m1_connsp_2('#skF_2','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_239])).

tff(c_244,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_242])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n003.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 18:41:12 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.41/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.25  
% 2.41/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.25  %$ m1_connsp_2 > v4_pre_topc > v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.41/1.25  
% 2.41/1.25  %Foreground sorts:
% 2.41/1.25  
% 2.41/1.25  
% 2.41/1.25  %Background operators:
% 2.41/1.25  
% 2.41/1.25  
% 2.41/1.25  %Foreground operators:
% 2.41/1.25  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.41/1.25  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 2.41/1.25  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.41/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.41/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.41/1.25  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.41/1.25  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.41/1.25  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.41/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.41/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.41/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.41/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.41/1.25  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.41/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.41/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.41/1.25  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.41/1.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.41/1.25  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.41/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.41/1.25  
% 2.41/1.27  tff(f_102, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 2.41/1.27  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.41/1.27  tff(f_65, axiom, (![A, B]: ((((v2_pre_topc(A) & l1_pre_topc(A)) & v3_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k3_subset_1(u1_struct_0(A), B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_tops_1)).
% 2.41/1.27  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.41/1.27  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 2.41/1.27  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.41/1.27  tff(f_82, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 2.41/1.27  tff(c_18, plain, (~m1_connsp_2('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.41/1.27  tff(c_20, plain, (r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.41/1.27  tff(c_24, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.41/1.27  tff(c_32, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.41/1.27  tff(c_30, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.41/1.27  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.41/1.27  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.41/1.27  tff(c_34, plain, (![A_26, B_27]: (k3_subset_1(A_26, k3_subset_1(A_26, B_27))=B_27 | ~m1_subset_1(B_27, k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.41/1.27  tff(c_40, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_26, c_34])).
% 2.41/1.27  tff(c_22, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.41/1.27  tff(c_12, plain, (![A_11, B_12]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_11), B_12), A_11) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_11))) | ~v3_pre_topc(B_12, A_11) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.41/1.27  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k3_subset_1(A_1, B_2), k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.41/1.27  tff(c_125, plain, (![A_36, B_37]: (k3_subset_1(u1_struct_0(A_36), k2_pre_topc(A_36, k3_subset_1(u1_struct_0(A_36), B_37)))=k1_tops_1(A_36, B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.41/1.27  tff(c_153, plain, (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_40, c_125])).
% 2.41/1.27  tff(c_157, plain, (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_153])).
% 2.41/1.27  tff(c_158, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_157])).
% 2.41/1.27  tff(c_161, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_2, c_158])).
% 2.41/1.27  tff(c_165, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_161])).
% 2.41/1.27  tff(c_167, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_157])).
% 2.41/1.27  tff(c_6, plain, (![B_7, A_5]: (v4_pre_topc(B_7, A_5) | k2_pre_topc(A_5, B_7)!=B_7 | ~v2_pre_topc(A_5) | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0(A_5))) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.41/1.27  tff(c_170, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))!=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2') | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_167, c_6])).
% 2.41/1.27  tff(c_178, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))!=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_170])).
% 2.41/1.27  tff(c_206, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))!=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_178])).
% 2.41/1.27  tff(c_8, plain, (![A_5, B_7]: (k2_pre_topc(A_5, B_7)=B_7 | ~v4_pre_topc(B_7, A_5) | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0(A_5))) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.41/1.27  tff(c_173, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_167, c_8])).
% 2.41/1.27  tff(c_181, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_173])).
% 2.41/1.27  tff(c_207, plain, (~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_206, c_181])).
% 2.41/1.27  tff(c_210, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v3_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_207])).
% 2.41/1.27  tff(c_214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_22, c_26, c_210])).
% 2.41/1.27  tff(c_216, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_178])).
% 2.41/1.27  tff(c_10, plain, (![A_8, B_10]: (k3_subset_1(u1_struct_0(A_8), k2_pre_topc(A_8, k3_subset_1(u1_struct_0(A_8), B_10)))=k1_tops_1(A_8, B_10) | ~m1_subset_1(B_10, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.41/1.27  tff(c_221, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_216, c_10])).
% 2.41/1.27  tff(c_225, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_40, c_221])).
% 2.41/1.27  tff(c_14, plain, (![C_19, A_13, B_17]: (m1_connsp_2(C_19, A_13, B_17) | ~r2_hidden(B_17, k1_tops_1(A_13, C_19)) | ~m1_subset_1(C_19, k1_zfmisc_1(u1_struct_0(A_13))) | ~m1_subset_1(B_17, u1_struct_0(A_13)) | ~l1_pre_topc(A_13) | ~v2_pre_topc(A_13) | v2_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.41/1.27  tff(c_229, plain, (![B_17]: (m1_connsp_2('#skF_2', '#skF_1', B_17) | ~r2_hidden(B_17, '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_17, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_225, c_14])).
% 2.41/1.27  tff(c_233, plain, (![B_17]: (m1_connsp_2('#skF_2', '#skF_1', B_17) | ~r2_hidden(B_17, '#skF_2') | ~m1_subset_1(B_17, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_229])).
% 2.41/1.27  tff(c_236, plain, (![B_41]: (m1_connsp_2('#skF_2', '#skF_1', B_41) | ~r2_hidden(B_41, '#skF_2') | ~m1_subset_1(B_41, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_32, c_233])).
% 2.41/1.27  tff(c_239, plain, (m1_connsp_2('#skF_2', '#skF_1', '#skF_3') | ~r2_hidden('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_236])).
% 2.41/1.27  tff(c_242, plain, (m1_connsp_2('#skF_2', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_239])).
% 2.41/1.27  tff(c_244, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_242])).
% 2.41/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.27  
% 2.41/1.27  Inference rules
% 2.41/1.27  ----------------------
% 2.41/1.27  #Ref     : 0
% 2.41/1.27  #Sup     : 47
% 2.41/1.27  #Fact    : 0
% 2.41/1.27  #Define  : 0
% 2.41/1.27  #Split   : 5
% 2.41/1.27  #Chain   : 0
% 2.41/1.27  #Close   : 0
% 2.41/1.27  
% 2.41/1.27  Ordering : KBO
% 2.41/1.27  
% 2.41/1.27  Simplification rules
% 2.41/1.27  ----------------------
% 2.41/1.27  #Subsume      : 1
% 2.41/1.27  #Demod        : 30
% 2.41/1.27  #Tautology    : 20
% 2.41/1.27  #SimpNegUnit  : 5
% 2.41/1.27  #BackRed      : 0
% 2.41/1.27  
% 2.41/1.27  #Partial instantiations: 0
% 2.41/1.27  #Strategies tried      : 1
% 2.41/1.27  
% 2.41/1.27  Timing (in seconds)
% 2.41/1.27  ----------------------
% 2.41/1.27  Preprocessing        : 0.30
% 2.41/1.27  Parsing              : 0.17
% 2.41/1.27  CNF conversion       : 0.02
% 2.41/1.27  Main loop            : 0.23
% 2.41/1.27  Inferencing          : 0.08
% 2.41/1.27  Reduction            : 0.07
% 2.41/1.27  Demodulation         : 0.05
% 2.41/1.27  BG Simplification    : 0.01
% 2.41/1.27  Subsumption          : 0.04
% 2.41/1.27  Abstraction          : 0.01
% 2.41/1.27  MUC search           : 0.00
% 2.41/1.27  Cooper               : 0.00
% 2.41/1.27  Total                : 0.57
% 2.41/1.27  Index Insertion      : 0.00
% 2.41/1.27  Index Deletion       : 0.00
% 2.41/1.27  Index Matching       : 0.00
% 2.41/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
