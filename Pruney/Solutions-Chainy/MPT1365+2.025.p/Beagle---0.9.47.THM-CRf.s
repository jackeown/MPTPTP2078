%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:57 EST 2020

% Result     : Theorem 5.93s
% Output     : CNFRefutation 5.93s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 122 expanded)
%              Number of leaves         :   30 (  59 expanded)
%              Depth                    :   10
%              Number of atoms          :  131 ( 354 expanded)
%              Number of equality atoms :    7 (  16 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v8_pre_topc,type,(
    v8_pre_topc: $i > $o )).

tff(v2_compts_1,type,(
    v2_compts_1: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_111,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v8_pre_topc(A)
                    & v2_compts_1(B,A)
                    & v2_compts_1(C,A) )
                 => v2_compts_1(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_compts_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v8_pre_topc(A)
              & v2_compts_1(B,A) )
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_compts_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v4_pre_topc(B,A)
                  & v4_pre_topc(C,A) )
               => v4_pre_topc(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tops_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_29,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_31,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_92,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v2_compts_1(B,A)
                  & r1_tarski(C,B)
                  & v4_pre_topc(C,A) )
               => v2_compts_1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_compts_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_93,plain,(
    ! [A_53,B_54,C_55] :
      ( k9_subset_1(A_53,B_54,C_55) = k3_xboole_0(B_54,C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_106,plain,(
    ! [B_54] : k9_subset_1(u1_struct_0('#skF_1'),B_54,'#skF_3') = k3_xboole_0(B_54,'#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_93])).

tff(c_24,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_138,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_24])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_30,plain,(
    v8_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_28,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_158,plain,(
    ! [B_63,A_64] :
      ( v4_pre_topc(B_63,A_64)
      | ~ v2_compts_1(B_63,A_64)
      | ~ v8_pre_topc(A_64)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64)
      | ~ v2_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_176,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_158])).

tff(c_189,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_30,c_28,c_176])).

tff(c_26,plain,(
    v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_173,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_compts_1('#skF_3','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_158])).

tff(c_186,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_30,c_26,c_173])).

tff(c_385,plain,(
    ! [A_94,B_95,C_96] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(A_94),B_95,C_96),A_94)
      | ~ v4_pre_topc(C_96,A_94)
      | ~ v4_pre_topc(B_95,A_94)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_398,plain,(
    ! [B_54] :
      ( v4_pre_topc(k3_xboole_0(B_54,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc('#skF_3','#skF_1')
      | ~ v4_pre_topc(B_54,'#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_385])).

tff(c_473,plain,(
    ! [B_104] :
      ( v4_pre_topc(k3_xboole_0(B_104,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc(B_104,'#skF_1')
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_32,c_186,c_398])).

tff(c_507,plain,
    ( v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_473])).

tff(c_525,plain,(
    v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_507])).

tff(c_139,plain,(
    ! [B_62] : k9_subset_1(u1_struct_0('#skF_1'),B_62,'#skF_3') = k3_xboole_0(B_62,'#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_93])).

tff(c_8,plain,(
    ! [A_5,B_6,C_7] :
      ( m1_subset_1(k9_subset_1(A_5,B_6,C_7),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(C_7,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_148,plain,(
    ! [B_62] :
      ( m1_subset_1(k3_xboole_0(B_62,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_8])).

tff(c_156,plain,(
    ! [B_62] : m1_subset_1(k3_xboole_0(B_62,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_148])).

tff(c_4,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_39,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_109,plain,(
    ! [A_56,B_57] : k9_subset_1(A_56,B_57,A_56) = k3_xboole_0(B_57,A_56) ),
    inference(resolution,[status(thm)],[c_39,c_93])).

tff(c_87,plain,(
    ! [A_47,B_48,C_49] :
      ( m1_subset_1(k9_subset_1(A_47,B_48,C_49),k1_zfmisc_1(A_47))
      | ~ m1_subset_1(C_49,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_91,plain,(
    ! [A_47,B_48,C_49] :
      ( r1_tarski(k9_subset_1(A_47,B_48,C_49),A_47)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(A_47)) ) ),
    inference(resolution,[status(thm)],[c_87,c_14])).

tff(c_115,plain,(
    ! [B_57,A_56] :
      ( r1_tarski(k3_xboole_0(B_57,A_56),A_56)
      | ~ m1_subset_1(A_56,k1_zfmisc_1(A_56)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_91])).

tff(c_124,plain,(
    ! [B_57,A_56] : r1_tarski(k3_xboole_0(B_57,A_56),A_56) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_115])).

tff(c_268,plain,(
    ! [C_74,A_75,B_76] :
      ( v2_compts_1(C_74,A_75)
      | ~ v4_pre_topc(C_74,A_75)
      | ~ r1_tarski(C_74,B_76)
      | ~ v2_compts_1(B_76,A_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2896,plain,(
    ! [B_441,A_442,A_443] :
      ( v2_compts_1(k3_xboole_0(B_441,A_442),A_443)
      | ~ v4_pre_topc(k3_xboole_0(B_441,A_442),A_443)
      | ~ v2_compts_1(A_442,A_443)
      | ~ m1_subset_1(k3_xboole_0(B_441,A_442),k1_zfmisc_1(u1_struct_0(A_443)))
      | ~ m1_subset_1(A_442,k1_zfmisc_1(u1_struct_0(A_443)))
      | ~ l1_pre_topc(A_443)
      | ~ v2_pre_topc(A_443) ) ),
    inference(resolution,[status(thm)],[c_124,c_268])).

tff(c_2960,plain,(
    ! [B_62] :
      ( v2_compts_1(k3_xboole_0(B_62,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0(B_62,'#skF_3'),'#skF_1')
      | ~ v2_compts_1('#skF_3','#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_156,c_2896])).

tff(c_3095,plain,(
    ! [B_450] :
      ( v2_compts_1(k3_xboole_0(B_450,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0(B_450,'#skF_3'),'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_32,c_26,c_2960])).

tff(c_3143,plain,(
    v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_525,c_3095])).

tff(c_3168,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_3143])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:42:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.93/2.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.93/2.16  
% 5.93/2.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.93/2.16  %$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 5.93/2.16  
% 5.93/2.16  %Foreground sorts:
% 5.93/2.16  
% 5.93/2.16  
% 5.93/2.16  %Background operators:
% 5.93/2.16  
% 5.93/2.16  
% 5.93/2.16  %Foreground operators:
% 5.93/2.16  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 5.93/2.16  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 5.93/2.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.93/2.16  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.93/2.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.93/2.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.93/2.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.93/2.16  tff('#skF_2', type, '#skF_2': $i).
% 5.93/2.16  tff('#skF_3', type, '#skF_3': $i).
% 5.93/2.16  tff('#skF_1', type, '#skF_1': $i).
% 5.93/2.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.93/2.16  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.93/2.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.93/2.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.93/2.16  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.93/2.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.93/2.16  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.93/2.16  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.93/2.16  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 5.93/2.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.93/2.16  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.93/2.16  
% 5.93/2.18  tff(f_111, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v8_pre_topc(A) & v2_compts_1(B, A)) & v2_compts_1(C, A)) => v2_compts_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_compts_1)).
% 5.93/2.18  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 5.93/2.18  tff(f_74, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v8_pre_topc(A) & v2_compts_1(B, A)) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_compts_1)).
% 5.93/2.18  tff(f_61, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & v4_pre_topc(C, A)) => v4_pre_topc(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tops_1)).
% 5.93/2.18  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 5.93/2.18  tff(f_29, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 5.93/2.18  tff(f_31, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 5.93/2.18  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.93/2.18  tff(f_92, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v2_compts_1(B, A) & r1_tarski(C, B)) & v4_pre_topc(C, A)) => v2_compts_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_compts_1)).
% 5.93/2.18  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.93/2.18  tff(c_93, plain, (![A_53, B_54, C_55]: (k9_subset_1(A_53, B_54, C_55)=k3_xboole_0(B_54, C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.93/2.18  tff(c_106, plain, (![B_54]: (k9_subset_1(u1_struct_0('#skF_1'), B_54, '#skF_3')=k3_xboole_0(B_54, '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_93])).
% 5.93/2.18  tff(c_24, plain, (~v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.93/2.18  tff(c_138, plain, (~v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_24])).
% 5.93/2.18  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.93/2.18  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.93/2.18  tff(c_30, plain, (v8_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.93/2.18  tff(c_28, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.93/2.18  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.93/2.18  tff(c_158, plain, (![B_63, A_64]: (v4_pre_topc(B_63, A_64) | ~v2_compts_1(B_63, A_64) | ~v8_pre_topc(A_64) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64) | ~v2_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.93/2.18  tff(c_176, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_158])).
% 5.93/2.18  tff(c_189, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_30, c_28, c_176])).
% 5.93/2.18  tff(c_26, plain, (v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.93/2.18  tff(c_173, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_158])).
% 5.93/2.18  tff(c_186, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_30, c_26, c_173])).
% 5.93/2.18  tff(c_385, plain, (![A_94, B_95, C_96]: (v4_pre_topc(k9_subset_1(u1_struct_0(A_94), B_95, C_96), A_94) | ~v4_pre_topc(C_96, A_94) | ~v4_pre_topc(B_95, A_94) | ~m1_subset_1(C_96, k1_zfmisc_1(u1_struct_0(A_94))) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94) | ~v2_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.93/2.18  tff(c_398, plain, (![B_54]: (v4_pre_topc(k3_xboole_0(B_54, '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1') | ~v4_pre_topc(B_54, '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_106, c_385])).
% 5.93/2.18  tff(c_473, plain, (![B_104]: (v4_pre_topc(k3_xboole_0(B_104, '#skF_3'), '#skF_1') | ~v4_pre_topc(B_104, '#skF_1') | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_32, c_186, c_398])).
% 5.93/2.18  tff(c_507, plain, (v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_473])).
% 5.93/2.18  tff(c_525, plain, (v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_189, c_507])).
% 5.93/2.18  tff(c_139, plain, (![B_62]: (k9_subset_1(u1_struct_0('#skF_1'), B_62, '#skF_3')=k3_xboole_0(B_62, '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_93])).
% 5.93/2.18  tff(c_8, plain, (![A_5, B_6, C_7]: (m1_subset_1(k9_subset_1(A_5, B_6, C_7), k1_zfmisc_1(A_5)) | ~m1_subset_1(C_7, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.93/2.18  tff(c_148, plain, (![B_62]: (m1_subset_1(k3_xboole_0(B_62, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_139, c_8])).
% 5.93/2.18  tff(c_156, plain, (![B_62]: (m1_subset_1(k3_xboole_0(B_62, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_148])).
% 5.93/2.18  tff(c_4, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.93/2.18  tff(c_6, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.93/2.18  tff(c_39, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 5.93/2.18  tff(c_109, plain, (![A_56, B_57]: (k9_subset_1(A_56, B_57, A_56)=k3_xboole_0(B_57, A_56))), inference(resolution, [status(thm)], [c_39, c_93])).
% 5.93/2.18  tff(c_87, plain, (![A_47, B_48, C_49]: (m1_subset_1(k9_subset_1(A_47, B_48, C_49), k1_zfmisc_1(A_47)) | ~m1_subset_1(C_49, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.93/2.18  tff(c_14, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.93/2.18  tff(c_91, plain, (![A_47, B_48, C_49]: (r1_tarski(k9_subset_1(A_47, B_48, C_49), A_47) | ~m1_subset_1(C_49, k1_zfmisc_1(A_47)))), inference(resolution, [status(thm)], [c_87, c_14])).
% 5.93/2.18  tff(c_115, plain, (![B_57, A_56]: (r1_tarski(k3_xboole_0(B_57, A_56), A_56) | ~m1_subset_1(A_56, k1_zfmisc_1(A_56)))), inference(superposition, [status(thm), theory('equality')], [c_109, c_91])).
% 5.93/2.18  tff(c_124, plain, (![B_57, A_56]: (r1_tarski(k3_xboole_0(B_57, A_56), A_56))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_115])).
% 5.93/2.18  tff(c_268, plain, (![C_74, A_75, B_76]: (v2_compts_1(C_74, A_75) | ~v4_pre_topc(C_74, A_75) | ~r1_tarski(C_74, B_76) | ~v2_compts_1(B_76, A_75) | ~m1_subset_1(C_74, k1_zfmisc_1(u1_struct_0(A_75))) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.93/2.18  tff(c_2896, plain, (![B_441, A_442, A_443]: (v2_compts_1(k3_xboole_0(B_441, A_442), A_443) | ~v4_pre_topc(k3_xboole_0(B_441, A_442), A_443) | ~v2_compts_1(A_442, A_443) | ~m1_subset_1(k3_xboole_0(B_441, A_442), k1_zfmisc_1(u1_struct_0(A_443))) | ~m1_subset_1(A_442, k1_zfmisc_1(u1_struct_0(A_443))) | ~l1_pre_topc(A_443) | ~v2_pre_topc(A_443))), inference(resolution, [status(thm)], [c_124, c_268])).
% 5.93/2.18  tff(c_2960, plain, (![B_62]: (v2_compts_1(k3_xboole_0(B_62, '#skF_3'), '#skF_1') | ~v4_pre_topc(k3_xboole_0(B_62, '#skF_3'), '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_156, c_2896])).
% 5.93/2.18  tff(c_3095, plain, (![B_450]: (v2_compts_1(k3_xboole_0(B_450, '#skF_3'), '#skF_1') | ~v4_pre_topc(k3_xboole_0(B_450, '#skF_3'), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_32, c_26, c_2960])).
% 5.93/2.18  tff(c_3143, plain, (v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_525, c_3095])).
% 5.93/2.18  tff(c_3168, plain, $false, inference(negUnitSimplification, [status(thm)], [c_138, c_3143])).
% 5.93/2.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.93/2.18  
% 5.93/2.18  Inference rules
% 5.93/2.18  ----------------------
% 5.93/2.18  #Ref     : 0
% 5.93/2.18  #Sup     : 660
% 5.93/2.18  #Fact    : 0
% 5.93/2.18  #Define  : 0
% 5.93/2.18  #Split   : 1
% 5.93/2.18  #Chain   : 0
% 5.93/2.18  #Close   : 0
% 5.93/2.18  
% 5.93/2.18  Ordering : KBO
% 5.93/2.18  
% 5.93/2.18  Simplification rules
% 5.93/2.18  ----------------------
% 5.93/2.18  #Subsume      : 65
% 5.93/2.18  #Demod        : 1002
% 5.93/2.18  #Tautology    : 181
% 5.93/2.18  #SimpNegUnit  : 1
% 5.93/2.18  #BackRed      : 1
% 5.93/2.18  
% 5.93/2.18  #Partial instantiations: 0
% 5.93/2.18  #Strategies tried      : 1
% 5.93/2.18  
% 5.93/2.18  Timing (in seconds)
% 5.93/2.18  ----------------------
% 5.93/2.18  Preprocessing        : 0.32
% 5.93/2.18  Parsing              : 0.18
% 5.93/2.18  CNF conversion       : 0.02
% 5.93/2.18  Main loop            : 1.07
% 5.93/2.18  Inferencing          : 0.37
% 5.93/2.18  Reduction            : 0.42
% 5.93/2.18  Demodulation         : 0.34
% 5.93/2.18  BG Simplification    : 0.04
% 5.93/2.18  Subsumption          : 0.17
% 5.93/2.18  Abstraction          : 0.06
% 5.93/2.18  MUC search           : 0.00
% 5.93/2.18  Cooper               : 0.00
% 5.93/2.18  Total                : 1.43
% 5.93/2.18  Index Insertion      : 0.00
% 5.93/2.18  Index Deletion       : 0.00
% 5.93/2.18  Index Matching       : 0.00
% 5.93/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
