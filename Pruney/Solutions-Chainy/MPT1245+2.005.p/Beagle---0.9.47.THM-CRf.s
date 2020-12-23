%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:50 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 384 expanded)
%              Number of leaves         :   28 ( 146 expanded)
%              Depth                    :   14
%              Number of atoms          :   91 ( 747 expanded)
%              Number of equality atoms :   32 ( 226 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
             => k2_pre_topc(A,k1_tops_1(A,k2_pre_topc(A,B))) = k2_pre_topc(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tops_1)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v3_pre_topc(B,A)
             => k2_pre_topc(A,k7_subset_1(u1_struct_0(A),k2_struct_0(A),B)) = k7_subset_1(u1_struct_0(A),k2_struct_0(A),B) )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,k7_subset_1(u1_struct_0(A),k2_struct_0(A),B)) = k7_subset_1(u1_struct_0(A),k2_struct_0(A),B) )
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_pre_topc)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,k1_tops_1(A,B)) = k2_pre_topc(A,k1_tops_1(A,k2_pre_topc(A,k1_tops_1(A,B)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_tops_1)).

tff(c_22,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) != k2_pre_topc('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_12,plain,(
    ! [A_10] :
      ( l1_struct_0(A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_30,plain,(
    ! [A_22] :
      ( u1_struct_0(A_22) = k2_struct_0(A_22)
      | ~ l1_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_36,plain,(
    ! [A_24] :
      ( u1_struct_0(A_24) = k2_struct_0(A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(resolution,[status(thm)],[c_12,c_30])).

tff(c_40,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_36])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_41,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_26])).

tff(c_64,plain,(
    ! [A_25,B_26] :
      ( k3_subset_1(A_25,k3_subset_1(A_25,B_26)) = B_26
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_72,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_41,c_64])).

tff(c_24,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_74,plain,(
    ! [A_27,B_28] :
      ( k4_xboole_0(A_27,B_28) = k3_subset_1(A_27,B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_85,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_41,c_74])).

tff(c_10,plain,(
    ! [A_9] :
      ( m1_subset_1(k2_struct_0(A_9),k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ l1_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_45,plain,
    ( m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_10])).

tff(c_49,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_45])).

tff(c_52,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_49])).

tff(c_56,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_52])).

tff(c_57,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_45])).

tff(c_103,plain,(
    ! [A_29,B_30,C_31] :
      ( k7_subset_1(A_29,B_30,C_31) = k4_xboole_0(B_30,C_31)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_110,plain,(
    ! [C_31] : k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),C_31) = k4_xboole_0(k2_struct_0('#skF_1'),C_31) ),
    inference(resolution,[status(thm)],[c_57,c_103])).

tff(c_246,plain,(
    ! [A_43,B_44] :
      ( k2_pre_topc(A_43,k7_subset_1(u1_struct_0(A_43),k2_struct_0(A_43),B_44)) = k7_subset_1(u1_struct_0(A_43),k2_struct_0(A_43),B_44)
      | ~ v3_pre_topc(B_44,A_43)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_258,plain,(
    ! [B_44] :
      ( k2_pre_topc('#skF_1',k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),B_44)) = k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),B_44)
      | ~ v3_pre_topc(B_44,'#skF_1')
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_246])).

tff(c_276,plain,(
    ! [B_47] :
      ( k2_pre_topc('#skF_1',k4_xboole_0(k2_struct_0('#skF_1'),B_47)) = k4_xboole_0(k2_struct_0('#skF_1'),B_47)
      | ~ v3_pre_topc(B_47,'#skF_1')
      | ~ m1_subset_1(B_47,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_40,c_110,c_110,c_40,c_258])).

tff(c_282,plain,
    ( k2_pre_topc('#skF_1',k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2')) = k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_41,c_276])).

tff(c_287,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_85,c_85,c_282])).

tff(c_164,plain,(
    ! [A_37,B_38] :
      ( k3_subset_1(u1_struct_0(A_37),k2_pre_topc(A_37,k3_subset_1(u1_struct_0(A_37),B_38))) = k1_tops_1(A_37,B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_182,plain,(
    ! [B_38] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),B_38))) = k1_tops_1('#skF_1',B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_164])).

tff(c_189,plain,(
    ! [B_38] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_38))) = k1_tops_1('#skF_1',B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_40,c_40,c_182])).

tff(c_291,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_189])).

tff(c_295,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_72,c_291])).

tff(c_20,plain,(
    ! [A_17,B_19] :
      ( k2_pre_topc(A_17,k1_tops_1(A_17,k2_pre_topc(A_17,k1_tops_1(A_17,B_19)))) = k2_pre_topc(A_17,k1_tops_1(A_17,B_19))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_300,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_20])).

tff(c_304,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_41,c_40,c_295,c_300])).

tff(c_306,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_304])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:11:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.35  
% 2.25/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.36  %$ v3_pre_topc > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.25/1.36  
% 2.25/1.36  %Foreground sorts:
% 2.25/1.36  
% 2.25/1.36  
% 2.25/1.36  %Background operators:
% 2.25/1.36  
% 2.25/1.36  
% 2.25/1.36  %Foreground operators:
% 2.25/1.36  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.25/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.25/1.36  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.25/1.36  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.25/1.36  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.25/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.25/1.36  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.25/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.25/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.25/1.36  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.25/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.36  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.25/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.25/1.36  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.25/1.36  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.25/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.25/1.36  
% 2.41/1.37  tff(f_88, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => (k2_pre_topc(A, k1_tops_1(A, k2_pre_topc(A, B))) = k2_pre_topc(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_tops_1)).
% 2.41/1.37  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.41/1.37  tff(f_41, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.41/1.37  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.41/1.37  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.41/1.37  tff(f_45, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 2.41/1.37  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.41/1.37  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) => (k2_pre_topc(A, k7_subset_1(u1_struct_0(A), k2_struct_0(A), B)) = k7_subset_1(u1_struct_0(A), k2_struct_0(A), B))) & ((v2_pre_topc(A) & (k2_pre_topc(A, k7_subset_1(u1_struct_0(A), k2_struct_0(A), B)) = k7_subset_1(u1_struct_0(A), k2_struct_0(A), B))) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_pre_topc)).
% 2.41/1.37  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 2.41/1.37  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, k1_tops_1(A, B)) = k2_pre_topc(A, k1_tops_1(A, k2_pre_topc(A, k1_tops_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_tops_1)).
% 2.41/1.37  tff(c_22, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))!=k2_pre_topc('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.41/1.37  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.41/1.37  tff(c_12, plain, (![A_10]: (l1_struct_0(A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.41/1.37  tff(c_30, plain, (![A_22]: (u1_struct_0(A_22)=k2_struct_0(A_22) | ~l1_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.41/1.37  tff(c_36, plain, (![A_24]: (u1_struct_0(A_24)=k2_struct_0(A_24) | ~l1_pre_topc(A_24))), inference(resolution, [status(thm)], [c_12, c_30])).
% 2.41/1.37  tff(c_40, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_28, c_36])).
% 2.41/1.37  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.41/1.37  tff(c_41, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_26])).
% 2.41/1.37  tff(c_64, plain, (![A_25, B_26]: (k3_subset_1(A_25, k3_subset_1(A_25, B_26))=B_26 | ~m1_subset_1(B_26, k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.41/1.37  tff(c_72, plain, (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_41, c_64])).
% 2.41/1.37  tff(c_24, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.41/1.37  tff(c_74, plain, (![A_27, B_28]: (k4_xboole_0(A_27, B_28)=k3_subset_1(A_27, B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.41/1.37  tff(c_85, plain, (k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2')=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_41, c_74])).
% 2.41/1.37  tff(c_10, plain, (![A_9]: (m1_subset_1(k2_struct_0(A_9), k1_zfmisc_1(u1_struct_0(A_9))) | ~l1_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.41/1.37  tff(c_45, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_40, c_10])).
% 2.41/1.37  tff(c_49, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_45])).
% 2.41/1.37  tff(c_52, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_49])).
% 2.41/1.37  tff(c_56, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_52])).
% 2.41/1.37  tff(c_57, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_45])).
% 2.41/1.37  tff(c_103, plain, (![A_29, B_30, C_31]: (k7_subset_1(A_29, B_30, C_31)=k4_xboole_0(B_30, C_31) | ~m1_subset_1(B_30, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.41/1.37  tff(c_110, plain, (![C_31]: (k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), C_31)=k4_xboole_0(k2_struct_0('#skF_1'), C_31))), inference(resolution, [status(thm)], [c_57, c_103])).
% 2.41/1.37  tff(c_246, plain, (![A_43, B_44]: (k2_pre_topc(A_43, k7_subset_1(u1_struct_0(A_43), k2_struct_0(A_43), B_44))=k7_subset_1(u1_struct_0(A_43), k2_struct_0(A_43), B_44) | ~v3_pre_topc(B_44, A_43) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.41/1.37  tff(c_258, plain, (![B_44]: (k2_pre_topc('#skF_1', k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), B_44))=k7_subset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_1'), B_44) | ~v3_pre_topc(B_44, '#skF_1') | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_246])).
% 2.41/1.37  tff(c_276, plain, (![B_47]: (k2_pre_topc('#skF_1', k4_xboole_0(k2_struct_0('#skF_1'), B_47))=k4_xboole_0(k2_struct_0('#skF_1'), B_47) | ~v3_pre_topc(B_47, '#skF_1') | ~m1_subset_1(B_47, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_40, c_110, c_110, c_40, c_258])).
% 2.41/1.37  tff(c_282, plain, (k2_pre_topc('#skF_1', k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2'))=k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_41, c_276])).
% 2.41/1.37  tff(c_287, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_85, c_85, c_282])).
% 2.41/1.37  tff(c_164, plain, (![A_37, B_38]: (k3_subset_1(u1_struct_0(A_37), k2_pre_topc(A_37, k3_subset_1(u1_struct_0(A_37), B_38)))=k1_tops_1(A_37, B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(A_37))) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.41/1.37  tff(c_182, plain, (![B_38]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), B_38)))=k1_tops_1('#skF_1', B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_164])).
% 2.41/1.37  tff(c_189, plain, (![B_38]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_38)))=k1_tops_1('#skF_1', B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_40, c_40, c_182])).
% 2.41/1.37  tff(c_291, plain, (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_287, c_189])).
% 2.41/1.37  tff(c_295, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_41, c_72, c_291])).
% 2.41/1.37  tff(c_20, plain, (![A_17, B_19]: (k2_pre_topc(A_17, k1_tops_1(A_17, k2_pre_topc(A_17, k1_tops_1(A_17, B_19))))=k2_pre_topc(A_17, k1_tops_1(A_17, B_19)) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.41/1.37  tff(c_300, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_295, c_20])).
% 2.41/1.37  tff(c_304, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_41, c_40, c_295, c_300])).
% 2.41/1.37  tff(c_306, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_304])).
% 2.41/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.37  
% 2.41/1.37  Inference rules
% 2.41/1.37  ----------------------
% 2.41/1.37  #Ref     : 0
% 2.41/1.37  #Sup     : 70
% 2.41/1.37  #Fact    : 0
% 2.41/1.37  #Define  : 0
% 2.41/1.37  #Split   : 3
% 2.41/1.37  #Chain   : 0
% 2.41/1.37  #Close   : 0
% 2.41/1.37  
% 2.41/1.37  Ordering : KBO
% 2.41/1.37  
% 2.41/1.37  Simplification rules
% 2.41/1.37  ----------------------
% 2.41/1.37  #Subsume      : 1
% 2.41/1.37  #Demod        : 41
% 2.41/1.37  #Tautology    : 39
% 2.41/1.37  #SimpNegUnit  : 1
% 2.41/1.37  #BackRed      : 1
% 2.41/1.37  
% 2.41/1.37  #Partial instantiations: 0
% 2.41/1.37  #Strategies tried      : 1
% 2.41/1.37  
% 2.41/1.37  Timing (in seconds)
% 2.41/1.37  ----------------------
% 2.41/1.37  Preprocessing        : 0.33
% 2.41/1.38  Parsing              : 0.18
% 2.41/1.38  CNF conversion       : 0.02
% 2.41/1.38  Main loop            : 0.21
% 2.41/1.38  Inferencing          : 0.08
% 2.41/1.38  Reduction            : 0.06
% 2.41/1.38  Demodulation         : 0.05
% 2.41/1.38  BG Simplification    : 0.02
% 2.41/1.38  Subsumption          : 0.03
% 2.41/1.38  Abstraction          : 0.01
% 2.41/1.38  MUC search           : 0.00
% 2.41/1.38  Cooper               : 0.00
% 2.41/1.38  Total                : 0.57
% 2.41/1.38  Index Insertion      : 0.00
% 2.41/1.38  Index Deletion       : 0.00
% 2.41/1.38  Index Matching       : 0.00
% 2.41/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
