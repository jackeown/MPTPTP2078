%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:55 EST 2020

% Result     : Theorem 8.93s
% Output     : CNFRefutation 8.93s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 114 expanded)
%              Number of leaves         :   33 (  58 expanded)
%              Depth                    :    9
%              Number of atoms          :  126 ( 336 expanded)
%              Number of equality atoms :   10 (  15 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_127,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_compts_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_90,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v8_pre_topc(A)
              & v2_compts_1(B,A) )
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_compts_1)).

tff(f_77,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tops_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_108,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_compts_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_736,plain,(
    ! [A_105,B_106,C_107] :
      ( k9_subset_1(A_105,B_106,C_107) = k3_xboole_0(B_106,C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(A_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_758,plain,(
    ! [B_106] : k9_subset_1(u1_struct_0('#skF_1'),B_106,'#skF_3') = k3_xboole_0(B_106,'#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_736])).

tff(c_34,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_819,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_758,c_34])).

tff(c_820,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_819])).

tff(c_48,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_40,plain,(
    v8_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_38,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_44,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_908,plain,(
    ! [B_116,A_117] :
      ( v4_pre_topc(B_116,A_117)
      | ~ v2_compts_1(B_116,A_117)
      | ~ v8_pre_topc(A_117)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_pre_topc(A_117)
      | ~ v2_pre_topc(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_941,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_908])).

tff(c_960,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_40,c_38,c_941])).

tff(c_36,plain,(
    v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_938,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_compts_1('#skF_3','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_908])).

tff(c_957,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_40,c_36,c_938])).

tff(c_1333,plain,(
    ! [A_129,B_130,C_131] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(A_129),B_130,C_131),A_129)
      | ~ v4_pre_topc(C_131,A_129)
      | ~ v4_pre_topc(B_130,A_129)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_pre_topc(A_129)
      | ~ v2_pre_topc(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1343,plain,(
    ! [B_106] :
      ( v4_pre_topc(k3_xboole_0(B_106,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc('#skF_3','#skF_1')
      | ~ v4_pre_topc(B_106,'#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_758,c_1333])).

tff(c_2529,plain,(
    ! [B_169] :
      ( v4_pre_topc(k3_xboole_0(B_169,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc(B_169,'#skF_1')
      | ~ m1_subset_1(B_169,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_42,c_957,c_1343])).

tff(c_2589,plain,
    ( v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_2529])).

tff(c_2630,plain,(
    v4_pre_topc(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_960,c_2,c_2589])).

tff(c_6,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_354,plain,(
    ! [A_77,B_78,C_79] :
      ( k7_subset_1(A_77,B_78,C_79) = k4_xboole_0(B_78,C_79)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_364,plain,(
    ! [C_79] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_3',C_79) = k4_xboole_0('#skF_3',C_79) ),
    inference(resolution,[status(thm)],[c_42,c_354])).

tff(c_509,plain,(
    ! [A_93,B_94,C_95] :
      ( m1_subset_1(k7_subset_1(A_93,B_94,C_95),k1_zfmisc_1(A_93))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_525,plain,(
    ! [C_79] :
      ( m1_subset_1(k4_xboole_0('#skF_3',C_79),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_364,c_509])).

tff(c_840,plain,(
    ! [C_114] : m1_subset_1(k4_xboole_0('#skF_3',C_114),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_525])).

tff(c_872,plain,(
    ! [B_6] : m1_subset_1(k3_xboole_0('#skF_3',B_6),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_840])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1097,plain,(
    ! [C_123,A_124,B_125] :
      ( v2_compts_1(C_123,A_124)
      | ~ v4_pre_topc(C_123,A_124)
      | ~ r1_tarski(C_123,B_125)
      | ~ v2_compts_1(B_125,A_124)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ l1_pre_topc(A_124)
      | ~ v2_pre_topc(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_4389,plain,(
    ! [A_221,B_222,A_223] :
      ( v2_compts_1(k3_xboole_0(A_221,B_222),A_223)
      | ~ v4_pre_topc(k3_xboole_0(A_221,B_222),A_223)
      | ~ v2_compts_1(A_221,A_223)
      | ~ m1_subset_1(k3_xboole_0(A_221,B_222),k1_zfmisc_1(u1_struct_0(A_223)))
      | ~ m1_subset_1(A_221,k1_zfmisc_1(u1_struct_0(A_223)))
      | ~ l1_pre_topc(A_223)
      | ~ v2_pre_topc(A_223) ) ),
    inference(resolution,[status(thm)],[c_4,c_1097])).

tff(c_4413,plain,(
    ! [B_6] :
      ( v2_compts_1(k3_xboole_0('#skF_3',B_6),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0('#skF_3',B_6),'#skF_1')
      | ~ v2_compts_1('#skF_3','#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_872,c_4389])).

tff(c_14728,plain,(
    ! [B_468] :
      ( v2_compts_1(k3_xboole_0('#skF_3',B_468),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0('#skF_3',B_468),'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_42,c_36,c_4413])).

tff(c_14750,plain,(
    v2_compts_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_2630,c_14728])).

tff(c_14786,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_820,c_14750])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n011.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 16:46:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.93/3.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.93/3.56  
% 8.93/3.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.93/3.56  %$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 8.93/3.56  
% 8.93/3.56  %Foreground sorts:
% 8.93/3.56  
% 8.93/3.56  
% 8.93/3.56  %Background operators:
% 8.93/3.56  
% 8.93/3.56  
% 8.93/3.56  %Foreground operators:
% 8.93/3.56  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 8.93/3.56  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 8.93/3.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.93/3.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.93/3.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.93/3.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.93/3.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.93/3.56  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 8.93/3.56  tff('#skF_2', type, '#skF_2': $i).
% 8.93/3.56  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 8.93/3.56  tff('#skF_3', type, '#skF_3': $i).
% 8.93/3.56  tff('#skF_1', type, '#skF_1': $i).
% 8.93/3.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.93/3.56  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 8.93/3.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.93/3.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.93/3.56  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.93/3.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.93/3.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.93/3.56  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 8.93/3.56  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 8.93/3.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.93/3.56  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.93/3.56  
% 8.93/3.58  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.93/3.58  tff(f_127, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v8_pre_topc(A) & v2_compts_1(B, A)) & v2_compts_1(C, A)) => v2_compts_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_compts_1)).
% 8.93/3.58  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 8.93/3.58  tff(f_90, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v8_pre_topc(A) & v2_compts_1(B, A)) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_compts_1)).
% 8.93/3.58  tff(f_77, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & v4_pre_topc(C, A)) => v4_pre_topc(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tops_1)).
% 8.93/3.58  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.93/3.58  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 8.93/3.58  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 8.93/3.58  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 8.93/3.58  tff(f_108, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v2_compts_1(B, A) & r1_tarski(C, B)) & v4_pre_topc(C, A)) => v2_compts_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_compts_1)).
% 8.93/3.58  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.93/3.58  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.93/3.58  tff(c_736, plain, (![A_105, B_106, C_107]: (k9_subset_1(A_105, B_106, C_107)=k3_xboole_0(B_106, C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(A_105)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.93/3.58  tff(c_758, plain, (![B_106]: (k9_subset_1(u1_struct_0('#skF_1'), B_106, '#skF_3')=k3_xboole_0(B_106, '#skF_3'))), inference(resolution, [status(thm)], [c_42, c_736])).
% 8.93/3.58  tff(c_34, plain, (~v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.93/3.58  tff(c_819, plain, (~v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_758, c_34])).
% 8.93/3.58  tff(c_820, plain, (~v2_compts_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_819])).
% 8.93/3.58  tff(c_48, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.93/3.58  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.93/3.58  tff(c_40, plain, (v8_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.93/3.58  tff(c_38, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.93/3.58  tff(c_44, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.93/3.58  tff(c_908, plain, (![B_116, A_117]: (v4_pre_topc(B_116, A_117) | ~v2_compts_1(B_116, A_117) | ~v8_pre_topc(A_117) | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0(A_117))) | ~l1_pre_topc(A_117) | ~v2_pre_topc(A_117))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.93/3.58  tff(c_941, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_908])).
% 8.93/3.58  tff(c_960, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_40, c_38, c_941])).
% 8.93/3.58  tff(c_36, plain, (v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.93/3.58  tff(c_938, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_908])).
% 8.93/3.58  tff(c_957, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_40, c_36, c_938])).
% 8.93/3.58  tff(c_1333, plain, (![A_129, B_130, C_131]: (v4_pre_topc(k9_subset_1(u1_struct_0(A_129), B_130, C_131), A_129) | ~v4_pre_topc(C_131, A_129) | ~v4_pre_topc(B_130, A_129) | ~m1_subset_1(C_131, k1_zfmisc_1(u1_struct_0(A_129))) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(A_129))) | ~l1_pre_topc(A_129) | ~v2_pre_topc(A_129))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.93/3.58  tff(c_1343, plain, (![B_106]: (v4_pre_topc(k3_xboole_0(B_106, '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1') | ~v4_pre_topc(B_106, '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_758, c_1333])).
% 8.93/3.58  tff(c_2529, plain, (![B_169]: (v4_pre_topc(k3_xboole_0(B_169, '#skF_3'), '#skF_1') | ~v4_pre_topc(B_169, '#skF_1') | ~m1_subset_1(B_169, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_42, c_957, c_1343])).
% 8.93/3.58  tff(c_2589, plain, (v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_44, c_2529])).
% 8.93/3.58  tff(c_2630, plain, (v4_pre_topc(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_960, c_2, c_2589])).
% 8.93/3.58  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k4_xboole_0(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.93/3.58  tff(c_354, plain, (![A_77, B_78, C_79]: (k7_subset_1(A_77, B_78, C_79)=k4_xboole_0(B_78, C_79) | ~m1_subset_1(B_78, k1_zfmisc_1(A_77)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.93/3.58  tff(c_364, plain, (![C_79]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_3', C_79)=k4_xboole_0('#skF_3', C_79))), inference(resolution, [status(thm)], [c_42, c_354])).
% 8.93/3.58  tff(c_509, plain, (![A_93, B_94, C_95]: (m1_subset_1(k7_subset_1(A_93, B_94, C_95), k1_zfmisc_1(A_93)) | ~m1_subset_1(B_94, k1_zfmisc_1(A_93)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.93/3.58  tff(c_525, plain, (![C_79]: (m1_subset_1(k4_xboole_0('#skF_3', C_79), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_364, c_509])).
% 8.93/3.58  tff(c_840, plain, (![C_114]: (m1_subset_1(k4_xboole_0('#skF_3', C_114), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_525])).
% 8.93/3.58  tff(c_872, plain, (![B_6]: (m1_subset_1(k3_xboole_0('#skF_3', B_6), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_6, c_840])).
% 8.93/3.58  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.93/3.58  tff(c_1097, plain, (![C_123, A_124, B_125]: (v2_compts_1(C_123, A_124) | ~v4_pre_topc(C_123, A_124) | ~r1_tarski(C_123, B_125) | ~v2_compts_1(B_125, A_124) | ~m1_subset_1(C_123, k1_zfmisc_1(u1_struct_0(A_124))) | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_124))) | ~l1_pre_topc(A_124) | ~v2_pre_topc(A_124))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.93/3.58  tff(c_4389, plain, (![A_221, B_222, A_223]: (v2_compts_1(k3_xboole_0(A_221, B_222), A_223) | ~v4_pre_topc(k3_xboole_0(A_221, B_222), A_223) | ~v2_compts_1(A_221, A_223) | ~m1_subset_1(k3_xboole_0(A_221, B_222), k1_zfmisc_1(u1_struct_0(A_223))) | ~m1_subset_1(A_221, k1_zfmisc_1(u1_struct_0(A_223))) | ~l1_pre_topc(A_223) | ~v2_pre_topc(A_223))), inference(resolution, [status(thm)], [c_4, c_1097])).
% 8.93/3.58  tff(c_4413, plain, (![B_6]: (v2_compts_1(k3_xboole_0('#skF_3', B_6), '#skF_1') | ~v4_pre_topc(k3_xboole_0('#skF_3', B_6), '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_872, c_4389])).
% 8.93/3.58  tff(c_14728, plain, (![B_468]: (v2_compts_1(k3_xboole_0('#skF_3', B_468), '#skF_1') | ~v4_pre_topc(k3_xboole_0('#skF_3', B_468), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_42, c_36, c_4413])).
% 8.93/3.58  tff(c_14750, plain, (v2_compts_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_2630, c_14728])).
% 8.93/3.58  tff(c_14786, plain, $false, inference(negUnitSimplification, [status(thm)], [c_820, c_14750])).
% 8.93/3.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.93/3.58  
% 8.93/3.58  Inference rules
% 8.93/3.58  ----------------------
% 8.93/3.58  #Ref     : 0
% 8.93/3.58  #Sup     : 3434
% 8.93/3.58  #Fact    : 0
% 8.93/3.58  #Define  : 0
% 8.93/3.58  #Split   : 0
% 8.93/3.58  #Chain   : 0
% 8.93/3.58  #Close   : 0
% 8.93/3.58  
% 8.93/3.58  Ordering : KBO
% 8.93/3.58  
% 8.93/3.58  Simplification rules
% 8.93/3.58  ----------------------
% 8.93/3.58  #Subsume      : 37
% 8.93/3.58  #Demod        : 3121
% 8.93/3.58  #Tautology    : 1612
% 8.93/3.58  #SimpNegUnit  : 1
% 8.93/3.58  #BackRed      : 14
% 8.93/3.58  
% 8.93/3.58  #Partial instantiations: 0
% 8.93/3.58  #Strategies tried      : 1
% 8.93/3.58  
% 8.93/3.58  Timing (in seconds)
% 8.93/3.58  ----------------------
% 8.93/3.58  Preprocessing        : 0.32
% 8.93/3.58  Parsing              : 0.17
% 8.93/3.58  CNF conversion       : 0.02
% 8.93/3.58  Main loop            : 2.50
% 8.93/3.58  Inferencing          : 0.53
% 8.93/3.58  Reduction            : 1.32
% 8.93/3.58  Demodulation         : 1.14
% 8.93/3.58  BG Simplification    : 0.07
% 8.93/3.58  Subsumption          : 0.42
% 8.93/3.58  Abstraction          : 0.11
% 8.93/3.58  MUC search           : 0.00
% 8.93/3.58  Cooper               : 0.00
% 8.93/3.58  Total                : 2.85
% 8.93/3.58  Index Insertion      : 0.00
% 8.93/3.58  Index Deletion       : 0.00
% 8.93/3.58  Index Matching       : 0.00
% 8.93/3.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
