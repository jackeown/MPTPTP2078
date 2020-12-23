%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:49 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.81s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 123 expanded)
%              Number of leaves         :   27 (  52 expanded)
%              Depth                    :    8
%              Number of atoms          :  147 ( 357 expanded)
%              Number of equality atoms :   24 (  54 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r1_tarski(C,B)
                      & v3_pre_topc(C,A) )
                   => C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(c_36,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_57,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_495,plain,(
    ! [B_74,A_75] :
      ( v2_tops_1(B_74,A_75)
      | k1_tops_1(A_75,B_74) != k1_xboole_0
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_502,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_495])).

tff(c_506,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_502])).

tff(c_507,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_506])).

tff(c_300,plain,(
    ! [A_63,B_64] :
      ( r1_tarski(k1_tops_1(A_63,B_64),B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_305,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_300])).

tff(c_309,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_305])).

tff(c_34,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_808,plain,(
    ! [A_85,B_86] :
      ( v3_pre_topc(k1_tops_1(A_85,B_86),A_85)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85)
      | ~ v2_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_813,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_808])).

tff(c_817,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_813])).

tff(c_59,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | ~ m1_subset_1(A_38,k1_zfmisc_1(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_63,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_59])).

tff(c_223,plain,(
    ! [A_55,C_56,B_57] :
      ( r1_tarski(A_55,C_56)
      | ~ r1_tarski(B_57,C_56)
      | ~ r1_tarski(A_55,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_236,plain,(
    ! [A_55] :
      ( r1_tarski(A_55,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_55,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_63,c_223])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_54,plain,(
    ! [C_34] :
      ( v2_tops_1('#skF_2','#skF_1')
      | k1_xboole_0 = C_34
      | ~ v3_pre_topc(C_34,'#skF_1')
      | ~ r1_tarski(C_34,'#skF_2')
      | ~ m1_subset_1(C_34,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_376,plain,(
    ! [C_68] :
      ( k1_xboole_0 = C_68
      | ~ v3_pre_topc(C_68,'#skF_1')
      | ~ r1_tarski(C_68,'#skF_2')
      | ~ m1_subset_1(C_68,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_54])).

tff(c_1022,plain,(
    ! [A_99] :
      ( k1_xboole_0 = A_99
      | ~ v3_pre_topc(A_99,'#skF_1')
      | ~ r1_tarski(A_99,'#skF_2')
      | ~ r1_tarski(A_99,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_18,c_376])).

tff(c_1066,plain,(
    ! [A_100] :
      ( k1_xboole_0 = A_100
      | ~ v3_pre_topc(A_100,'#skF_1')
      | ~ r1_tarski(A_100,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_236,c_1022])).

tff(c_1069,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_817,c_1066])).

tff(c_1075,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_1069])).

tff(c_1077,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_507,c_1075])).

tff(c_1078,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1079,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_38,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1084,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1079,c_38])).

tff(c_40,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1082,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1079,c_40])).

tff(c_42,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1104,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1079,c_42])).

tff(c_1448,plain,(
    ! [A_129,B_130] :
      ( k1_tops_1(A_129,B_130) = k1_xboole_0
      | ~ v2_tops_1(B_130,A_129)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_pre_topc(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1458,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1448])).

tff(c_1465,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1079,c_1458])).

tff(c_2190,plain,(
    ! [B_154,A_155,C_156] :
      ( r1_tarski(B_154,k1_tops_1(A_155,C_156))
      | ~ r1_tarski(B_154,C_156)
      | ~ v3_pre_topc(B_154,A_155)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(u1_struct_0(A_155)))
      | ~ m1_subset_1(B_154,k1_zfmisc_1(u1_struct_0(A_155)))
      | ~ l1_pre_topc(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2197,plain,(
    ! [B_154] :
      ( r1_tarski(B_154,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_154,'#skF_2')
      | ~ v3_pre_topc(B_154,'#skF_1')
      | ~ m1_subset_1(B_154,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_2190])).

tff(c_2486,plain,(
    ! [B_161] :
      ( r1_tarski(B_161,k1_xboole_0)
      | ~ r1_tarski(B_161,'#skF_2')
      | ~ v3_pre_topc(B_161,'#skF_1')
      | ~ m1_subset_1(B_161,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1465,c_2197])).

tff(c_2493,plain,
    ( r1_tarski('#skF_3',k1_xboole_0)
    | ~ r1_tarski('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_1104,c_2486])).

tff(c_2500,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1084,c_1082,c_2493])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1086,plain,(
    ! [A_105,B_106] :
      ( k4_xboole_0(A_105,B_106) = k1_xboole_0
      | ~ r1_tarski(A_105,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1116,plain,(
    ! [B_107] : k4_xboole_0(B_107,B_107) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_1086])).

tff(c_14,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1121,plain,(
    ! [B_107] : r1_tarski(k1_xboole_0,B_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_1116,c_14])).

tff(c_1237,plain,(
    ! [B_116,A_117] :
      ( B_116 = A_117
      | ~ r1_tarski(B_116,A_117)
      | ~ r1_tarski(A_117,B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1254,plain,(
    ! [B_107] :
      ( k1_xboole_0 = B_107
      | ~ r1_tarski(B_107,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1121,c_1237])).

tff(c_2508,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2500,c_1254])).

tff(c_2520,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1078,c_2508])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:06:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.39/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.62  
% 3.39/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.62  %$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.39/1.62  
% 3.39/1.62  %Foreground sorts:
% 3.39/1.62  
% 3.39/1.62  
% 3.39/1.62  %Background operators:
% 3.39/1.62  
% 3.39/1.62  
% 3.39/1.62  %Foreground operators:
% 3.39/1.62  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.39/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.39/1.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.39/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.39/1.62  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.39/1.62  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.39/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.39/1.62  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.39/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.39/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.39/1.62  tff('#skF_1', type, '#skF_1': $i).
% 3.39/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.39/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.39/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.39/1.62  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.39/1.62  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.39/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.39/1.62  
% 3.81/1.63  tff(f_104, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tops_1)).
% 3.81/1.63  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 3.81/1.63  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 3.81/1.63  tff(f_55, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 3.81/1.63  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.81/1.63  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.81/1.63  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 3.81/1.63  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.81/1.63  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.81/1.63  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.81/1.63  tff(c_36, plain, (k1_xboole_0!='#skF_3' | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.81/1.63  tff(c_57, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_36])).
% 3.81/1.63  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.81/1.63  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.81/1.63  tff(c_495, plain, (![B_74, A_75]: (v2_tops_1(B_74, A_75) | k1_tops_1(A_75, B_74)!=k1_xboole_0 | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.81/1.63  tff(c_502, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_495])).
% 3.81/1.63  tff(c_506, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_502])).
% 3.81/1.63  tff(c_507, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_57, c_506])).
% 3.81/1.63  tff(c_300, plain, (![A_63, B_64]: (r1_tarski(k1_tops_1(A_63, B_64), B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.81/1.63  tff(c_305, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_300])).
% 3.81/1.63  tff(c_309, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_305])).
% 3.81/1.63  tff(c_34, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.81/1.63  tff(c_808, plain, (![A_85, B_86]: (v3_pre_topc(k1_tops_1(A_85, B_86), A_85) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85) | ~v2_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.81/1.63  tff(c_813, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_808])).
% 3.81/1.63  tff(c_817, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_813])).
% 3.81/1.63  tff(c_59, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | ~m1_subset_1(A_38, k1_zfmisc_1(B_39)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.81/1.63  tff(c_63, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_59])).
% 3.81/1.63  tff(c_223, plain, (![A_55, C_56, B_57]: (r1_tarski(A_55, C_56) | ~r1_tarski(B_57, C_56) | ~r1_tarski(A_55, B_57))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.81/1.63  tff(c_236, plain, (![A_55]: (r1_tarski(A_55, u1_struct_0('#skF_1')) | ~r1_tarski(A_55, '#skF_2'))), inference(resolution, [status(thm)], [c_63, c_223])).
% 3.81/1.63  tff(c_18, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.81/1.63  tff(c_54, plain, (![C_34]: (v2_tops_1('#skF_2', '#skF_1') | k1_xboole_0=C_34 | ~v3_pre_topc(C_34, '#skF_1') | ~r1_tarski(C_34, '#skF_2') | ~m1_subset_1(C_34, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.81/1.63  tff(c_376, plain, (![C_68]: (k1_xboole_0=C_68 | ~v3_pre_topc(C_68, '#skF_1') | ~r1_tarski(C_68, '#skF_2') | ~m1_subset_1(C_68, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_57, c_54])).
% 3.81/1.63  tff(c_1022, plain, (![A_99]: (k1_xboole_0=A_99 | ~v3_pre_topc(A_99, '#skF_1') | ~r1_tarski(A_99, '#skF_2') | ~r1_tarski(A_99, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_18, c_376])).
% 3.81/1.63  tff(c_1066, plain, (![A_100]: (k1_xboole_0=A_100 | ~v3_pre_topc(A_100, '#skF_1') | ~r1_tarski(A_100, '#skF_2'))), inference(resolution, [status(thm)], [c_236, c_1022])).
% 3.81/1.63  tff(c_1069, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_817, c_1066])).
% 3.81/1.63  tff(c_1075, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_309, c_1069])).
% 3.81/1.63  tff(c_1077, plain, $false, inference(negUnitSimplification, [status(thm)], [c_507, c_1075])).
% 3.81/1.63  tff(c_1078, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_36])).
% 3.81/1.63  tff(c_1079, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_36])).
% 3.81/1.63  tff(c_38, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.81/1.63  tff(c_1084, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1079, c_38])).
% 3.81/1.63  tff(c_40, plain, (r1_tarski('#skF_3', '#skF_2') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.81/1.63  tff(c_1082, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1079, c_40])).
% 3.81/1.63  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.81/1.63  tff(c_1104, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1079, c_42])).
% 3.81/1.63  tff(c_1448, plain, (![A_129, B_130]: (k1_tops_1(A_129, B_130)=k1_xboole_0 | ~v2_tops_1(B_130, A_129) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(A_129))) | ~l1_pre_topc(A_129))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.81/1.63  tff(c_1458, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1448])).
% 3.81/1.63  tff(c_1465, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1079, c_1458])).
% 3.81/1.63  tff(c_2190, plain, (![B_154, A_155, C_156]: (r1_tarski(B_154, k1_tops_1(A_155, C_156)) | ~r1_tarski(B_154, C_156) | ~v3_pre_topc(B_154, A_155) | ~m1_subset_1(C_156, k1_zfmisc_1(u1_struct_0(A_155))) | ~m1_subset_1(B_154, k1_zfmisc_1(u1_struct_0(A_155))) | ~l1_pre_topc(A_155))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.81/1.63  tff(c_2197, plain, (![B_154]: (r1_tarski(B_154, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_154, '#skF_2') | ~v3_pre_topc(B_154, '#skF_1') | ~m1_subset_1(B_154, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_2190])).
% 3.81/1.63  tff(c_2486, plain, (![B_161]: (r1_tarski(B_161, k1_xboole_0) | ~r1_tarski(B_161, '#skF_2') | ~v3_pre_topc(B_161, '#skF_1') | ~m1_subset_1(B_161, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1465, c_2197])).
% 3.81/1.63  tff(c_2493, plain, (r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_1104, c_2486])).
% 3.81/1.63  tff(c_2500, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1084, c_1082, c_2493])).
% 3.81/1.63  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.81/1.63  tff(c_1086, plain, (![A_105, B_106]: (k4_xboole_0(A_105, B_106)=k1_xboole_0 | ~r1_tarski(A_105, B_106))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.81/1.63  tff(c_1116, plain, (![B_107]: (k4_xboole_0(B_107, B_107)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_1086])).
% 3.81/1.63  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.81/1.63  tff(c_1121, plain, (![B_107]: (r1_tarski(k1_xboole_0, B_107))), inference(superposition, [status(thm), theory('equality')], [c_1116, c_14])).
% 3.81/1.63  tff(c_1237, plain, (![B_116, A_117]: (B_116=A_117 | ~r1_tarski(B_116, A_117) | ~r1_tarski(A_117, B_116))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.81/1.63  tff(c_1254, plain, (![B_107]: (k1_xboole_0=B_107 | ~r1_tarski(B_107, k1_xboole_0))), inference(resolution, [status(thm)], [c_1121, c_1237])).
% 3.81/1.63  tff(c_2508, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2500, c_1254])).
% 3.81/1.63  tff(c_2520, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1078, c_2508])).
% 3.81/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.81/1.63  
% 3.81/1.63  Inference rules
% 3.81/1.63  ----------------------
% 3.81/1.63  #Ref     : 0
% 3.81/1.63  #Sup     : 561
% 3.81/1.63  #Fact    : 0
% 3.81/1.63  #Define  : 0
% 3.81/1.63  #Split   : 9
% 3.81/1.63  #Chain   : 0
% 3.81/1.63  #Close   : 0
% 3.81/1.63  
% 3.81/1.63  Ordering : KBO
% 3.81/1.63  
% 3.81/1.63  Simplification rules
% 3.81/1.63  ----------------------
% 3.81/1.63  #Subsume      : 79
% 3.81/1.63  #Demod        : 380
% 3.81/1.63  #Tautology    : 338
% 3.81/1.63  #SimpNegUnit  : 7
% 3.81/1.63  #BackRed      : 2
% 3.81/1.63  
% 3.81/1.63  #Partial instantiations: 0
% 3.81/1.63  #Strategies tried      : 1
% 3.81/1.63  
% 3.81/1.63  Timing (in seconds)
% 3.81/1.63  ----------------------
% 3.81/1.64  Preprocessing        : 0.32
% 3.81/1.64  Parsing              : 0.17
% 3.81/1.64  CNF conversion       : 0.02
% 3.81/1.64  Main loop            : 0.53
% 3.81/1.64  Inferencing          : 0.18
% 3.81/1.64  Reduction            : 0.18
% 3.81/1.64  Demodulation         : 0.13
% 3.81/1.64  BG Simplification    : 0.02
% 3.81/1.64  Subsumption          : 0.11
% 3.81/1.64  Abstraction          : 0.02
% 3.81/1.64  MUC search           : 0.00
% 3.81/1.64  Cooper               : 0.00
% 3.81/1.64  Total                : 0.89
% 3.81/1.64  Index Insertion      : 0.00
% 3.81/1.64  Index Deletion       : 0.00
% 3.81/1.64  Index Matching       : 0.00
% 3.81/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
