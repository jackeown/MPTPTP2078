%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:58 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 100 expanded)
%              Number of leaves         :   28 (  50 expanded)
%              Depth                    :    9
%              Number of atoms          :  122 ( 316 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v8_pre_topc,type,(
    v8_pre_topc: $i > $o )).

tff(v2_compts_1,type,(
    v2_compts_1: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

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

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_105,negated_conjecture,(
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

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v8_pre_topc(A)
              & v2_compts_1(B,A) )
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_compts_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v4_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v4_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k3_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_tops_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_86,axiom,(
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

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_62,plain,(
    ! [A_37,B_38,C_39] :
      ( k9_subset_1(A_37,B_38,C_39) = k3_xboole_0(B_38,C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(A_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_68,plain,(
    ! [B_38] : k9_subset_1(u1_struct_0('#skF_1'),B_38,'#skF_3') = k3_xboole_0(B_38,'#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_62])).

tff(c_18,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_78,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_18])).

tff(c_32,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_24,plain,(
    v8_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_22,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_175,plain,(
    ! [B_54,A_55] :
      ( v4_pre_topc(B_54,A_55)
      | ~ v2_compts_1(B_54,A_55)
      | ~ v8_pre_topc(A_55)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_pre_topc(A_55)
      | ~ v2_pre_topc(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_194,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_175])).

tff(c_213,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_22,c_194])).

tff(c_20,plain,(
    v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_197,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_compts_1('#skF_3','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_175])).

tff(c_216,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_20,c_197])).

tff(c_261,plain,(
    ! [B_62,C_63,A_64] :
      ( v4_pre_topc(k3_xboole_0(B_62,C_63),A_64)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ v4_pre_topc(C_63,A_64)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ v4_pre_topc(B_62,A_64)
      | ~ l1_pre_topc(A_64)
      | ~ v2_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_276,plain,(
    ! [B_62] :
      ( v4_pre_topc(k3_xboole_0(B_62,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc('#skF_3','#skF_1')
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v4_pre_topc(B_62,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_261])).

tff(c_582,plain,(
    ! [B_83] :
      ( v4_pre_topc(k3_xboole_0(B_83,'#skF_3'),'#skF_1')
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v4_pre_topc(B_83,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_216,c_276])).

tff(c_613,plain,
    ( v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_582])).

tff(c_628,plain,(
    v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_613])).

tff(c_4,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k4_xboole_0(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_92,plain,(
    ! [A_45,B_46,C_47] :
      ( k7_subset_1(A_45,B_46,C_47) = k4_xboole_0(B_46,C_47)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_102,plain,(
    ! [C_48] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_48) = k4_xboole_0('#skF_2',C_48) ),
    inference(resolution,[status(thm)],[c_28,c_92])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] :
      ( m1_subset_1(k7_subset_1(A_5,B_6,C_7),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_108,plain,(
    ! [C_48] :
      ( m1_subset_1(k4_xboole_0('#skF_2',C_48),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_6])).

tff(c_130,plain,(
    ! [C_50] : m1_subset_1(k4_xboole_0('#skF_2',C_50),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_108])).

tff(c_142,plain,(
    ! [B_4] : m1_subset_1(k3_xboole_0('#skF_2',B_4),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_130])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_521,plain,(
    ! [C_76,A_77,B_78] :
      ( v2_compts_1(C_76,A_77)
      | ~ v4_pre_topc(C_76,A_77)
      | ~ r1_tarski(C_76,B_78)
      | ~ v2_compts_1(B_78,A_77)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1068,plain,(
    ! [A_120,B_121,A_122] :
      ( v2_compts_1(k3_xboole_0(A_120,B_121),A_122)
      | ~ v4_pre_topc(k3_xboole_0(A_120,B_121),A_122)
      | ~ v2_compts_1(A_120,A_122)
      | ~ m1_subset_1(k3_xboole_0(A_120,B_121),k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ m1_subset_1(A_120,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ l1_pre_topc(A_122)
      | ~ v2_pre_topc(A_122) ) ),
    inference(resolution,[status(thm)],[c_2,c_521])).

tff(c_1086,plain,(
    ! [B_4] :
      ( v2_compts_1(k3_xboole_0('#skF_2',B_4),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0('#skF_2',B_4),'#skF_1')
      | ~ v2_compts_1('#skF_2','#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_142,c_1068])).

tff(c_1119,plain,(
    ! [B_125] :
      ( v2_compts_1(k3_xboole_0('#skF_2',B_125),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0('#skF_2',B_125),'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_22,c_1086])).

tff(c_1122,plain,(
    v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_628,c_1119])).

tff(c_1132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1122])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:54:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.31/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.51  
% 3.31/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.51  %$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.31/1.51  
% 3.31/1.51  %Foreground sorts:
% 3.31/1.51  
% 3.31/1.51  
% 3.31/1.51  %Background operators:
% 3.31/1.51  
% 3.31/1.51  
% 3.31/1.51  %Foreground operators:
% 3.31/1.51  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 3.31/1.51  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 3.31/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.31/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.31/1.51  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.31/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.31/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.31/1.51  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.31/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.31/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.31/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.31/1.51  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.31/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.31/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.31/1.51  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.31/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.31/1.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.31/1.51  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.31/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.31/1.51  
% 3.31/1.52  tff(f_105, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v8_pre_topc(A) & v2_compts_1(B, A)) & v2_compts_1(C, A)) => v2_compts_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_compts_1)).
% 3.31/1.52  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.31/1.52  tff(f_68, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v8_pre_topc(A) & v2_compts_1(B, A)) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_compts_1)).
% 3.31/1.52  tff(f_55, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v4_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v4_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k3_xboole_0(B, C), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_tops_1)).
% 3.31/1.52  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.31/1.52  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.31/1.52  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 3.31/1.52  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.31/1.52  tff(f_86, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v2_compts_1(B, A) & r1_tarski(C, B)) & v4_pre_topc(C, A)) => v2_compts_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_compts_1)).
% 3.31/1.52  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.31/1.52  tff(c_62, plain, (![A_37, B_38, C_39]: (k9_subset_1(A_37, B_38, C_39)=k3_xboole_0(B_38, C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.31/1.52  tff(c_68, plain, (![B_38]: (k9_subset_1(u1_struct_0('#skF_1'), B_38, '#skF_3')=k3_xboole_0(B_38, '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_62])).
% 3.31/1.52  tff(c_18, plain, (~v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.31/1.52  tff(c_78, plain, (~v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_18])).
% 3.31/1.52  tff(c_32, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.31/1.52  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.31/1.52  tff(c_24, plain, (v8_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.31/1.52  tff(c_22, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.31/1.52  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.31/1.52  tff(c_175, plain, (![B_54, A_55]: (v4_pre_topc(B_54, A_55) | ~v2_compts_1(B_54, A_55) | ~v8_pre_topc(A_55) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_pre_topc(A_55) | ~v2_pre_topc(A_55))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.31/1.52  tff(c_194, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_175])).
% 3.31/1.52  tff(c_213, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_22, c_194])).
% 3.31/1.52  tff(c_20, plain, (v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.31/1.52  tff(c_197, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_175])).
% 3.31/1.52  tff(c_216, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_20, c_197])).
% 3.31/1.52  tff(c_261, plain, (![B_62, C_63, A_64]: (v4_pre_topc(k3_xboole_0(B_62, C_63), A_64) | ~m1_subset_1(C_63, k1_zfmisc_1(u1_struct_0(A_64))) | ~v4_pre_topc(C_63, A_64) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_64))) | ~v4_pre_topc(B_62, A_64) | ~l1_pre_topc(A_64) | ~v2_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.31/1.52  tff(c_276, plain, (![B_62]: (v4_pre_topc(k3_xboole_0(B_62, '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1') | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v4_pre_topc(B_62, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_261])).
% 3.31/1.52  tff(c_582, plain, (![B_83]: (v4_pre_topc(k3_xboole_0(B_83, '#skF_3'), '#skF_1') | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v4_pre_topc(B_83, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_216, c_276])).
% 3.31/1.52  tff(c_613, plain, (v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_28, c_582])).
% 3.31/1.52  tff(c_628, plain, (v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_213, c_613])).
% 3.31/1.52  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k4_xboole_0(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.31/1.52  tff(c_92, plain, (![A_45, B_46, C_47]: (k7_subset_1(A_45, B_46, C_47)=k4_xboole_0(B_46, C_47) | ~m1_subset_1(B_46, k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.31/1.52  tff(c_102, plain, (![C_48]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_48)=k4_xboole_0('#skF_2', C_48))), inference(resolution, [status(thm)], [c_28, c_92])).
% 3.31/1.52  tff(c_6, plain, (![A_5, B_6, C_7]: (m1_subset_1(k7_subset_1(A_5, B_6, C_7), k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.31/1.52  tff(c_108, plain, (![C_48]: (m1_subset_1(k4_xboole_0('#skF_2', C_48), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_102, c_6])).
% 3.31/1.52  tff(c_130, plain, (![C_50]: (m1_subset_1(k4_xboole_0('#skF_2', C_50), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_108])).
% 3.31/1.52  tff(c_142, plain, (![B_4]: (m1_subset_1(k3_xboole_0('#skF_2', B_4), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_4, c_130])).
% 3.31/1.52  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.31/1.52  tff(c_521, plain, (![C_76, A_77, B_78]: (v2_compts_1(C_76, A_77) | ~v4_pre_topc(C_76, A_77) | ~r1_tarski(C_76, B_78) | ~v2_compts_1(B_78, A_77) | ~m1_subset_1(C_76, k1_zfmisc_1(u1_struct_0(A_77))) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77) | ~v2_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.31/1.52  tff(c_1068, plain, (![A_120, B_121, A_122]: (v2_compts_1(k3_xboole_0(A_120, B_121), A_122) | ~v4_pre_topc(k3_xboole_0(A_120, B_121), A_122) | ~v2_compts_1(A_120, A_122) | ~m1_subset_1(k3_xboole_0(A_120, B_121), k1_zfmisc_1(u1_struct_0(A_122))) | ~m1_subset_1(A_120, k1_zfmisc_1(u1_struct_0(A_122))) | ~l1_pre_topc(A_122) | ~v2_pre_topc(A_122))), inference(resolution, [status(thm)], [c_2, c_521])).
% 3.31/1.52  tff(c_1086, plain, (![B_4]: (v2_compts_1(k3_xboole_0('#skF_2', B_4), '#skF_1') | ~v4_pre_topc(k3_xboole_0('#skF_2', B_4), '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_142, c_1068])).
% 3.31/1.52  tff(c_1119, plain, (![B_125]: (v2_compts_1(k3_xboole_0('#skF_2', B_125), '#skF_1') | ~v4_pre_topc(k3_xboole_0('#skF_2', B_125), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_22, c_1086])).
% 3.31/1.52  tff(c_1122, plain, (v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_628, c_1119])).
% 3.31/1.52  tff(c_1132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_1122])).
% 3.31/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.52  
% 3.31/1.52  Inference rules
% 3.31/1.52  ----------------------
% 3.31/1.52  #Ref     : 0
% 3.31/1.52  #Sup     : 245
% 3.31/1.52  #Fact    : 0
% 3.31/1.52  #Define  : 0
% 3.31/1.52  #Split   : 0
% 3.31/1.52  #Chain   : 0
% 3.31/1.52  #Close   : 0
% 3.31/1.52  
% 3.31/1.52  Ordering : KBO
% 3.31/1.52  
% 3.31/1.52  Simplification rules
% 3.31/1.52  ----------------------
% 3.31/1.52  #Subsume      : 8
% 3.31/1.52  #Demod        : 214
% 3.31/1.52  #Tautology    : 56
% 3.31/1.52  #SimpNegUnit  : 1
% 3.31/1.52  #BackRed      : 1
% 3.31/1.52  
% 3.31/1.52  #Partial instantiations: 0
% 3.31/1.52  #Strategies tried      : 1
% 3.31/1.52  
% 3.31/1.52  Timing (in seconds)
% 3.31/1.52  ----------------------
% 3.31/1.52  Preprocessing        : 0.30
% 3.31/1.52  Parsing              : 0.16
% 3.31/1.52  CNF conversion       : 0.02
% 3.31/1.52  Main loop            : 0.43
% 3.31/1.52  Inferencing          : 0.15
% 3.31/1.52  Reduction            : 0.16
% 3.31/1.52  Demodulation         : 0.12
% 3.31/1.52  BG Simplification    : 0.02
% 3.31/1.52  Subsumption          : 0.06
% 3.31/1.52  Abstraction          : 0.03
% 3.31/1.53  MUC search           : 0.00
% 3.31/1.53  Cooper               : 0.00
% 3.31/1.53  Total                : 0.76
% 3.31/1.53  Index Insertion      : 0.00
% 3.31/1.53  Index Deletion       : 0.00
% 3.31/1.53  Index Matching       : 0.00
% 3.31/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
