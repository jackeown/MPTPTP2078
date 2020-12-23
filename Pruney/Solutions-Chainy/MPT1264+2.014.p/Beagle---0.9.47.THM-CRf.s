%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:40 EST 2020

% Result     : Theorem 3.66s
% Output     : CNFRefutation 4.01s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 191 expanded)
%              Number of leaves         :   35 (  83 expanded)
%              Depth                    :   12
%              Number of atoms          :  107 ( 422 expanded)
%              Number of equality atoms :   29 ( 101 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v1_tops_1(B,A)
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( v3_pre_topc(C,A)
                   => k2_pre_topc(A,C) = k2_pre_topc(A,k9_subset_1(u1_struct_0(A),C,B)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tops_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_38,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( v3_pre_topc(B,A)
               => k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,C))) = k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tops_1)).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_22,plain,(
    ! [A_20] :
      ( l1_struct_0(A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_55,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_60,plain,(
    ! [A_39] :
      ( u1_struct_0(A_39) = k2_struct_0(A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(resolution,[status(thm)],[c_22,c_55])).

tff(c_64,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_60])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_67,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_38])).

tff(c_111,plain,(
    ! [A_56,B_57,C_58] :
      ( k9_subset_1(A_56,B_57,C_58) = k3_xboole_0(B_57,C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_118,plain,(
    ! [B_57] : k9_subset_1(k2_struct_0('#skF_2'),B_57,'#skF_3') = k3_xboole_0(B_57,'#skF_3') ),
    inference(resolution,[status(thm)],[c_67,c_111])).

tff(c_30,plain,(
    k2_pre_topc('#skF_2',k9_subset_1(u1_struct_0('#skF_2'),'#skF_4','#skF_3')) != k2_pre_topc('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_65,plain,(
    k2_pre_topc('#skF_2',k9_subset_1(k2_struct_0('#skF_2'),'#skF_4','#skF_3')) != k2_pre_topc('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_30])).

tff(c_150,plain,(
    k2_pre_topc('#skF_2',k3_xboole_0('#skF_4','#skF_3')) != k2_pre_topc('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_65])).

tff(c_32,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_34])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_107,plain,(
    ! [C_53,A_54,B_55] :
      ( r2_hidden(C_53,A_54)
      | ~ r2_hidden(C_53,B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_179,plain,(
    ! [A_69,B_70,A_71] :
      ( r2_hidden('#skF_1'(A_69,B_70),A_71)
      | ~ m1_subset_1(A_69,k1_zfmisc_1(A_71))
      | r1_tarski(A_69,B_70) ) ),
    inference(resolution,[status(thm)],[c_6,c_107])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_202,plain,(
    ! [A_74,A_75] :
      ( ~ m1_subset_1(A_74,k1_zfmisc_1(A_75))
      | r1_tarski(A_74,A_75) ) ),
    inference(resolution,[status(thm)],[c_179,c_4])).

tff(c_213,plain,(
    r1_tarski('#skF_4',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_202])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_223,plain,(
    k3_xboole_0('#skF_4',k2_struct_0('#skF_2')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_213,c_8])).

tff(c_42,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_10,plain,(
    ! [A_8] : k2_subset_1(A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12,plain,(
    ! [A_9] : m1_subset_1(k2_subset_1(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_43,plain,(
    ! [A_9] : m1_subset_1(A_9,k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_120,plain,(
    ! [A_9,B_57] : k9_subset_1(A_9,B_57,A_9) = k3_xboole_0(B_57,A_9) ),
    inference(resolution,[status(thm)],[c_43,c_111])).

tff(c_36,plain,(
    v1_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_191,plain,(
    ! [A_72,B_73] :
      ( k2_pre_topc(A_72,B_73) = k2_struct_0(A_72)
      | ~ v1_tops_1(B_73,A_72)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_194,plain,(
    ! [B_73] :
      ( k2_pre_topc('#skF_2',B_73) = k2_struct_0('#skF_2')
      | ~ v1_tops_1(B_73,'#skF_2')
      | ~ m1_subset_1(B_73,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_191])).

tff(c_280,plain,(
    ! [B_81] :
      ( k2_pre_topc('#skF_2',B_81) = k2_struct_0('#skF_2')
      | ~ v1_tops_1(B_81,'#skF_2')
      | ~ m1_subset_1(B_81,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_194])).

tff(c_283,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = k2_struct_0('#skF_2')
    | ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_67,c_280])).

tff(c_293,plain,(
    k2_pre_topc('#skF_2','#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_283])).

tff(c_28,plain,(
    ! [A_24,B_28,C_30] :
      ( k2_pre_topc(A_24,k9_subset_1(u1_struct_0(A_24),B_28,k2_pre_topc(A_24,C_30))) = k2_pre_topc(A_24,k9_subset_1(u1_struct_0(A_24),B_28,C_30))
      | ~ v3_pre_topc(B_28,A_24)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24)
      | ~ v2_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_302,plain,(
    ! [B_28] :
      ( k2_pre_topc('#skF_2',k9_subset_1(u1_struct_0('#skF_2'),B_28,k2_struct_0('#skF_2'))) = k2_pre_topc('#skF_2',k9_subset_1(u1_struct_0('#skF_2'),B_28,'#skF_3'))
      | ~ v3_pre_topc(B_28,'#skF_2')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_28])).

tff(c_1049,plain,(
    ! [B_196] :
      ( k2_pre_topc('#skF_2',k3_xboole_0(B_196,k2_struct_0('#skF_2'))) = k2_pre_topc('#skF_2',k3_xboole_0(B_196,'#skF_3'))
      | ~ v3_pre_topc(B_196,'#skF_2')
      | ~ m1_subset_1(B_196,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_64,c_67,c_64,c_118,c_120,c_64,c_64,c_302])).

tff(c_1055,plain,
    ( k2_pre_topc('#skF_2',k3_xboole_0('#skF_4',k2_struct_0('#skF_2'))) = k2_pre_topc('#skF_2',k3_xboole_0('#skF_4','#skF_3'))
    | ~ v3_pre_topc('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_1049])).

tff(c_1064,plain,(
    k2_pre_topc('#skF_2',k3_xboole_0('#skF_4','#skF_3')) = k2_pre_topc('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_223,c_1055])).

tff(c_1066,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_1064])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:24:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.66/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.66/1.63  
% 3.66/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.66/1.63  %$ v3_pre_topc > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.66/1.63  
% 3.66/1.63  %Foreground sorts:
% 3.66/1.63  
% 3.66/1.63  
% 3.66/1.63  %Background operators:
% 3.66/1.63  
% 3.66/1.63  
% 3.66/1.63  %Foreground operators:
% 3.66/1.63  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.66/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.66/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.66/1.63  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.66/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.66/1.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.66/1.63  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.66/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.66/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.66/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.66/1.63  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.66/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.66/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.66/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.66/1.63  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.66/1.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.66/1.63  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.66/1.63  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.66/1.63  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.66/1.63  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.66/1.63  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.66/1.63  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.66/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.66/1.63  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.66/1.63  
% 4.01/1.64  tff(f_101, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(C, A) => (k2_pre_topc(A, C) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), C, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_tops_1)).
% 4.01/1.64  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.01/1.64  tff(f_57, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 4.01/1.64  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.01/1.64  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.01/1.64  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 4.01/1.64  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.01/1.64  tff(f_38, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 4.01/1.64  tff(f_40, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.01/1.64  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 4.01/1.64  tff(f_84, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => (k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C))) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tops_1)).
% 4.01/1.64  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.01/1.64  tff(c_22, plain, (![A_20]: (l1_struct_0(A_20) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.01/1.64  tff(c_55, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.01/1.64  tff(c_60, plain, (![A_39]: (u1_struct_0(A_39)=k2_struct_0(A_39) | ~l1_pre_topc(A_39))), inference(resolution, [status(thm)], [c_22, c_55])).
% 4.01/1.64  tff(c_64, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_60])).
% 4.01/1.64  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.01/1.64  tff(c_67, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_38])).
% 4.01/1.64  tff(c_111, plain, (![A_56, B_57, C_58]: (k9_subset_1(A_56, B_57, C_58)=k3_xboole_0(B_57, C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.01/1.64  tff(c_118, plain, (![B_57]: (k9_subset_1(k2_struct_0('#skF_2'), B_57, '#skF_3')=k3_xboole_0(B_57, '#skF_3'))), inference(resolution, [status(thm)], [c_67, c_111])).
% 4.01/1.64  tff(c_30, plain, (k2_pre_topc('#skF_2', k9_subset_1(u1_struct_0('#skF_2'), '#skF_4', '#skF_3'))!=k2_pre_topc('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.01/1.64  tff(c_65, plain, (k2_pre_topc('#skF_2', k9_subset_1(k2_struct_0('#skF_2'), '#skF_4', '#skF_3'))!=k2_pre_topc('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_30])).
% 4.01/1.64  tff(c_150, plain, (k2_pre_topc('#skF_2', k3_xboole_0('#skF_4', '#skF_3'))!=k2_pre_topc('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_65])).
% 4.01/1.64  tff(c_32, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.01/1.64  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.01/1.64  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_34])).
% 4.01/1.64  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.01/1.64  tff(c_107, plain, (![C_53, A_54, B_55]: (r2_hidden(C_53, A_54) | ~r2_hidden(C_53, B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.01/1.64  tff(c_179, plain, (![A_69, B_70, A_71]: (r2_hidden('#skF_1'(A_69, B_70), A_71) | ~m1_subset_1(A_69, k1_zfmisc_1(A_71)) | r1_tarski(A_69, B_70))), inference(resolution, [status(thm)], [c_6, c_107])).
% 4.01/1.64  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.01/1.64  tff(c_202, plain, (![A_74, A_75]: (~m1_subset_1(A_74, k1_zfmisc_1(A_75)) | r1_tarski(A_74, A_75))), inference(resolution, [status(thm)], [c_179, c_4])).
% 4.01/1.64  tff(c_213, plain, (r1_tarski('#skF_4', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_66, c_202])).
% 4.01/1.64  tff(c_8, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.01/1.64  tff(c_223, plain, (k3_xboole_0('#skF_4', k2_struct_0('#skF_2'))='#skF_4'), inference(resolution, [status(thm)], [c_213, c_8])).
% 4.01/1.64  tff(c_42, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.01/1.64  tff(c_10, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.01/1.64  tff(c_12, plain, (![A_9]: (m1_subset_1(k2_subset_1(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.01/1.64  tff(c_43, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 4.01/1.64  tff(c_120, plain, (![A_9, B_57]: (k9_subset_1(A_9, B_57, A_9)=k3_xboole_0(B_57, A_9))), inference(resolution, [status(thm)], [c_43, c_111])).
% 4.01/1.64  tff(c_36, plain, (v1_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.01/1.64  tff(c_191, plain, (![A_72, B_73]: (k2_pre_topc(A_72, B_73)=k2_struct_0(A_72) | ~v1_tops_1(B_73, A_72) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.01/1.64  tff(c_194, plain, (![B_73]: (k2_pre_topc('#skF_2', B_73)=k2_struct_0('#skF_2') | ~v1_tops_1(B_73, '#skF_2') | ~m1_subset_1(B_73, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_191])).
% 4.01/1.64  tff(c_280, plain, (![B_81]: (k2_pre_topc('#skF_2', B_81)=k2_struct_0('#skF_2') | ~v1_tops_1(B_81, '#skF_2') | ~m1_subset_1(B_81, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_194])).
% 4.01/1.64  tff(c_283, plain, (k2_pre_topc('#skF_2', '#skF_3')=k2_struct_0('#skF_2') | ~v1_tops_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_67, c_280])).
% 4.01/1.64  tff(c_293, plain, (k2_pre_topc('#skF_2', '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_283])).
% 4.01/1.64  tff(c_28, plain, (![A_24, B_28, C_30]: (k2_pre_topc(A_24, k9_subset_1(u1_struct_0(A_24), B_28, k2_pre_topc(A_24, C_30)))=k2_pre_topc(A_24, k9_subset_1(u1_struct_0(A_24), B_28, C_30)) | ~v3_pre_topc(B_28, A_24) | ~m1_subset_1(C_30, k1_zfmisc_1(u1_struct_0(A_24))) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24) | ~v2_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.01/1.64  tff(c_302, plain, (![B_28]: (k2_pre_topc('#skF_2', k9_subset_1(u1_struct_0('#skF_2'), B_28, k2_struct_0('#skF_2')))=k2_pre_topc('#skF_2', k9_subset_1(u1_struct_0('#skF_2'), B_28, '#skF_3')) | ~v3_pre_topc(B_28, '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_293, c_28])).
% 4.01/1.64  tff(c_1049, plain, (![B_196]: (k2_pre_topc('#skF_2', k3_xboole_0(B_196, k2_struct_0('#skF_2')))=k2_pre_topc('#skF_2', k3_xboole_0(B_196, '#skF_3')) | ~v3_pre_topc(B_196, '#skF_2') | ~m1_subset_1(B_196, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_64, c_67, c_64, c_118, c_120, c_64, c_64, c_302])).
% 4.01/1.64  tff(c_1055, plain, (k2_pre_topc('#skF_2', k3_xboole_0('#skF_4', k2_struct_0('#skF_2')))=k2_pre_topc('#skF_2', k3_xboole_0('#skF_4', '#skF_3')) | ~v3_pre_topc('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_1049])).
% 4.01/1.64  tff(c_1064, plain, (k2_pre_topc('#skF_2', k3_xboole_0('#skF_4', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_223, c_1055])).
% 4.01/1.64  tff(c_1066, plain, $false, inference(negUnitSimplification, [status(thm)], [c_150, c_1064])).
% 4.01/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.01/1.64  
% 4.01/1.64  Inference rules
% 4.01/1.64  ----------------------
% 4.01/1.64  #Ref     : 0
% 4.01/1.64  #Sup     : 252
% 4.01/1.64  #Fact    : 0
% 4.01/1.64  #Define  : 0
% 4.01/1.64  #Split   : 6
% 4.01/1.64  #Chain   : 0
% 4.01/1.64  #Close   : 0
% 4.01/1.64  
% 4.01/1.64  Ordering : KBO
% 4.01/1.64  
% 4.01/1.64  Simplification rules
% 4.01/1.64  ----------------------
% 4.01/1.64  #Subsume      : 87
% 4.01/1.64  #Demod        : 368
% 4.01/1.64  #Tautology    : 53
% 4.01/1.64  #SimpNegUnit  : 5
% 4.01/1.64  #BackRed      : 4
% 4.01/1.64  
% 4.01/1.64  #Partial instantiations: 0
% 4.01/1.64  #Strategies tried      : 1
% 4.01/1.64  
% 4.01/1.64  Timing (in seconds)
% 4.01/1.64  ----------------------
% 4.01/1.65  Preprocessing        : 0.31
% 4.01/1.65  Parsing              : 0.16
% 4.01/1.65  CNF conversion       : 0.02
% 4.01/1.65  Main loop            : 0.57
% 4.01/1.65  Inferencing          : 0.19
% 4.01/1.65  Reduction            : 0.20
% 4.01/1.65  Demodulation         : 0.15
% 4.01/1.65  BG Simplification    : 0.03
% 4.01/1.65  Subsumption          : 0.11
% 4.01/1.65  Abstraction          : 0.04
% 4.01/1.65  MUC search           : 0.00
% 4.01/1.65  Cooper               : 0.00
% 4.01/1.65  Total                : 0.91
% 4.01/1.65  Index Insertion      : 0.00
% 4.01/1.65  Index Deletion       : 0.00
% 4.01/1.65  Index Matching       : 0.00
% 4.01/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
