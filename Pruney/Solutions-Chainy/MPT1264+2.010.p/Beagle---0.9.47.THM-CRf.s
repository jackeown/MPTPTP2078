%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:39 EST 2020

% Result     : Theorem 4.04s
% Output     : CNFRefutation 4.22s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 200 expanded)
%              Number of leaves         :   37 (  86 expanded)
%              Depth                    :   12
%              Number of atoms          :  134 ( 455 expanded)
%              Number of equality atoms :   35 ( 108 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(f_116,negated_conjecture,(
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

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_66,axiom,(
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

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & ! [D] :
            ( ( r1_tarski(D,B)
              & r1_tarski(D,C) )
           => r1_tarski(D,A) ) )
     => A = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).

tff(f_53,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_55,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_99,axiom,(
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

tff(c_50,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_32,plain,(
    ! [A_24] :
      ( l1_struct_0(A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_67,plain,(
    ! [A_43] :
      ( u1_struct_0(A_43) = k2_struct_0(A_43)
      | ~ l1_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_72,plain,(
    ! [A_44] :
      ( u1_struct_0(A_44) = k2_struct_0(A_44)
      | ~ l1_pre_topc(A_44) ) ),
    inference(resolution,[status(thm)],[c_32,c_67])).

tff(c_76,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_72])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_78,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_48])).

tff(c_116,plain,(
    ! [A_59,B_60,C_61] :
      ( k9_subset_1(A_59,B_60,C_61) = k3_xboole_0(B_60,C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_123,plain,(
    ! [B_60] : k9_subset_1(k2_struct_0('#skF_3'),B_60,'#skF_4') = k3_xboole_0(B_60,'#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_116])).

tff(c_40,plain,(
    k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),'#skF_5','#skF_4')) != k2_pre_topc('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_107,plain,(
    k2_pre_topc('#skF_3',k9_subset_1(k2_struct_0('#skF_3'),'#skF_5','#skF_4')) != k2_pre_topc('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_40])).

tff(c_135,plain,(
    k2_pre_topc('#skF_3',k3_xboole_0('#skF_5','#skF_4')) != k2_pre_topc('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_107])).

tff(c_42,plain,(
    v3_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_77,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_44])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_112,plain,(
    ! [C_56,A_57,B_58] :
      ( r2_hidden(C_56,A_57)
      | ~ r2_hidden(C_56,B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_210,plain,(
    ! [A_74,B_75,A_76] :
      ( r2_hidden('#skF_1'(A_74,B_75),A_76)
      | ~ m1_subset_1(A_74,k1_zfmisc_1(A_76))
      | r1_tarski(A_74,B_75) ) ),
    inference(resolution,[status(thm)],[c_6,c_112])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_222,plain,(
    ! [A_77,A_78] :
      ( ~ m1_subset_1(A_77,k1_zfmisc_1(A_78))
      | r1_tarski(A_77,A_78) ) ),
    inference(resolution,[status(thm)],[c_210,c_4])).

tff(c_233,plain,(
    r1_tarski('#skF_5',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_77,c_222])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_18,plain,(
    ! [A_8,B_9,C_10] :
      ( r1_tarski('#skF_2'(A_8,B_9,C_10),B_9)
      | k3_xboole_0(B_9,C_10) = A_8
      | ~ r1_tarski(A_8,C_10)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_340,plain,(
    ! [A_95,B_96,C_97] :
      ( ~ r1_tarski('#skF_2'(A_95,B_96,C_97),A_95)
      | k3_xboole_0(B_96,C_97) = A_95
      | ~ r1_tarski(A_95,C_97)
      | ~ r1_tarski(A_95,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_348,plain,(
    ! [B_9,C_10] :
      ( k3_xboole_0(B_9,C_10) = B_9
      | ~ r1_tarski(B_9,C_10)
      | ~ r1_tarski(B_9,B_9) ) ),
    inference(resolution,[status(thm)],[c_18,c_340])).

tff(c_353,plain,(
    ! [B_98,C_99] :
      ( k3_xboole_0(B_98,C_99) = B_98
      | ~ r1_tarski(B_98,C_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_348])).

tff(c_371,plain,(
    k3_xboole_0('#skF_5',k2_struct_0('#skF_3')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_233,c_353])).

tff(c_20,plain,(
    ! [A_12] : k2_subset_1(A_12) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_22,plain,(
    ! [A_13] : m1_subset_1(k2_subset_1(A_13),k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_53,plain,(
    ! [A_13] : m1_subset_1(A_13,k1_zfmisc_1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_125,plain,(
    ! [A_13,B_60] : k9_subset_1(A_13,B_60,A_13) = k3_xboole_0(B_60,A_13) ),
    inference(resolution,[status(thm)],[c_53,c_116])).

tff(c_46,plain,(
    v1_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_145,plain,(
    ! [A_65,B_66] :
      ( k2_pre_topc(A_65,B_66) = k2_struct_0(A_65)
      | ~ v1_tops_1(B_66,A_65)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_148,plain,(
    ! [B_66] :
      ( k2_pre_topc('#skF_3',B_66) = k2_struct_0('#skF_3')
      | ~ v1_tops_1(B_66,'#skF_3')
      | ~ m1_subset_1(B_66,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_145])).

tff(c_177,plain,(
    ! [B_71] :
      ( k2_pre_topc('#skF_3',B_71) = k2_struct_0('#skF_3')
      | ~ v1_tops_1(B_71,'#skF_3')
      | ~ m1_subset_1(B_71,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_148])).

tff(c_180,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = k2_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_177])).

tff(c_190,plain,(
    k2_pre_topc('#skF_3','#skF_4') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_180])).

tff(c_52,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_749,plain,(
    ! [A_127,B_128,C_129] :
      ( k2_pre_topc(A_127,k9_subset_1(u1_struct_0(A_127),B_128,k2_pre_topc(A_127,C_129))) = k2_pre_topc(A_127,k9_subset_1(u1_struct_0(A_127),B_128,C_129))
      | ~ v3_pre_topc(B_128,A_127)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_pre_topc(A_127)
      | ~ v2_pre_topc(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_767,plain,(
    ! [B_128,C_129] :
      ( k2_pre_topc('#skF_3',k9_subset_1(k2_struct_0('#skF_3'),B_128,k2_pre_topc('#skF_3',C_129))) = k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),B_128,C_129))
      | ~ v3_pre_topc(B_128,'#skF_3')
      | ~ m1_subset_1(C_129,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_749])).

tff(c_1008,plain,(
    ! [B_151,C_152] :
      ( k2_pre_topc('#skF_3',k9_subset_1(k2_struct_0('#skF_3'),B_151,k2_pre_topc('#skF_3',C_152))) = k2_pre_topc('#skF_3',k9_subset_1(k2_struct_0('#skF_3'),B_151,C_152))
      | ~ v3_pre_topc(B_151,'#skF_3')
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(B_151,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_76,c_76,c_76,c_767])).

tff(c_1030,plain,(
    ! [B_151] :
      ( k2_pre_topc('#skF_3',k9_subset_1(k2_struct_0('#skF_3'),B_151,k2_struct_0('#skF_3'))) = k2_pre_topc('#skF_3',k9_subset_1(k2_struct_0('#skF_3'),B_151,'#skF_4'))
      | ~ v3_pre_topc(B_151,'#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(B_151,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_1008])).

tff(c_1338,plain,(
    ! [B_215] :
      ( k2_pre_topc('#skF_3',k3_xboole_0(B_215,k2_struct_0('#skF_3'))) = k2_pre_topc('#skF_3',k3_xboole_0(B_215,'#skF_4'))
      | ~ v3_pre_topc(B_215,'#skF_3')
      | ~ m1_subset_1(B_215,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_123,c_125,c_1030])).

tff(c_1344,plain,
    ( k2_pre_topc('#skF_3',k3_xboole_0('#skF_5',k2_struct_0('#skF_3'))) = k2_pre_topc('#skF_3',k3_xboole_0('#skF_5','#skF_4'))
    | ~ v3_pre_topc('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_77,c_1338])).

tff(c_1353,plain,(
    k2_pre_topc('#skF_3',k3_xboole_0('#skF_5','#skF_4')) = k2_pre_topc('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_371,c_1344])).

tff(c_1355,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_1353])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:25:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.04/1.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.04/1.80  
% 4.04/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.04/1.80  %$ v3_pre_topc > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 4.04/1.80  
% 4.04/1.80  %Foreground sorts:
% 4.04/1.80  
% 4.04/1.80  
% 4.04/1.80  %Background operators:
% 4.04/1.80  
% 4.04/1.80  
% 4.04/1.80  %Foreground operators:
% 4.04/1.80  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.04/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.04/1.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.04/1.80  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.04/1.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.04/1.80  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.04/1.80  tff('#skF_5', type, '#skF_5': $i).
% 4.04/1.80  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 4.04/1.80  tff('#skF_3', type, '#skF_3': $i).
% 4.04/1.80  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.04/1.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.04/1.80  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.04/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.04/1.80  tff('#skF_4', type, '#skF_4': $i).
% 4.04/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.04/1.80  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.04/1.80  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.04/1.80  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.04/1.80  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.04/1.80  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.04/1.80  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.04/1.80  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.04/1.80  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.04/1.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.04/1.80  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.04/1.80  
% 4.22/1.82  tff(f_116, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(C, A) => (k2_pre_topc(A, C) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), C, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_tops_1)).
% 4.22/1.82  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.22/1.82  tff(f_72, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 4.22/1.82  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.22/1.82  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.22/1.82  tff(f_62, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 4.22/1.82  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.22/1.82  tff(f_51, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & (![D]: ((r1_tarski(D, B) & r1_tarski(D, C)) => r1_tarski(D, A)))) => (A = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_xboole_1)).
% 4.22/1.82  tff(f_53, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 4.22/1.82  tff(f_55, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.22/1.82  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 4.22/1.82  tff(f_99, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => (k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C))) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tops_1)).
% 4.22/1.82  tff(c_50, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.22/1.82  tff(c_32, plain, (![A_24]: (l1_struct_0(A_24) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.22/1.82  tff(c_67, plain, (![A_43]: (u1_struct_0(A_43)=k2_struct_0(A_43) | ~l1_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.22/1.82  tff(c_72, plain, (![A_44]: (u1_struct_0(A_44)=k2_struct_0(A_44) | ~l1_pre_topc(A_44))), inference(resolution, [status(thm)], [c_32, c_67])).
% 4.22/1.82  tff(c_76, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_72])).
% 4.22/1.82  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.22/1.82  tff(c_78, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_48])).
% 4.22/1.82  tff(c_116, plain, (![A_59, B_60, C_61]: (k9_subset_1(A_59, B_60, C_61)=k3_xboole_0(B_60, C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.22/1.82  tff(c_123, plain, (![B_60]: (k9_subset_1(k2_struct_0('#skF_3'), B_60, '#skF_4')=k3_xboole_0(B_60, '#skF_4'))), inference(resolution, [status(thm)], [c_78, c_116])).
% 4.22/1.82  tff(c_40, plain, (k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), '#skF_5', '#skF_4'))!=k2_pre_topc('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.22/1.82  tff(c_107, plain, (k2_pre_topc('#skF_3', k9_subset_1(k2_struct_0('#skF_3'), '#skF_5', '#skF_4'))!=k2_pre_topc('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_40])).
% 4.22/1.82  tff(c_135, plain, (k2_pre_topc('#skF_3', k3_xboole_0('#skF_5', '#skF_4'))!=k2_pre_topc('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_107])).
% 4.22/1.82  tff(c_42, plain, (v3_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.22/1.82  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.22/1.82  tff(c_77, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_44])).
% 4.22/1.82  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.22/1.82  tff(c_112, plain, (![C_56, A_57, B_58]: (r2_hidden(C_56, A_57) | ~r2_hidden(C_56, B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.22/1.82  tff(c_210, plain, (![A_74, B_75, A_76]: (r2_hidden('#skF_1'(A_74, B_75), A_76) | ~m1_subset_1(A_74, k1_zfmisc_1(A_76)) | r1_tarski(A_74, B_75))), inference(resolution, [status(thm)], [c_6, c_112])).
% 4.22/1.82  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.22/1.82  tff(c_222, plain, (![A_77, A_78]: (~m1_subset_1(A_77, k1_zfmisc_1(A_78)) | r1_tarski(A_77, A_78))), inference(resolution, [status(thm)], [c_210, c_4])).
% 4.22/1.82  tff(c_233, plain, (r1_tarski('#skF_5', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_77, c_222])).
% 4.22/1.82  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.22/1.82  tff(c_18, plain, (![A_8, B_9, C_10]: (r1_tarski('#skF_2'(A_8, B_9, C_10), B_9) | k3_xboole_0(B_9, C_10)=A_8 | ~r1_tarski(A_8, C_10) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.22/1.82  tff(c_340, plain, (![A_95, B_96, C_97]: (~r1_tarski('#skF_2'(A_95, B_96, C_97), A_95) | k3_xboole_0(B_96, C_97)=A_95 | ~r1_tarski(A_95, C_97) | ~r1_tarski(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.22/1.82  tff(c_348, plain, (![B_9, C_10]: (k3_xboole_0(B_9, C_10)=B_9 | ~r1_tarski(B_9, C_10) | ~r1_tarski(B_9, B_9))), inference(resolution, [status(thm)], [c_18, c_340])).
% 4.22/1.82  tff(c_353, plain, (![B_98, C_99]: (k3_xboole_0(B_98, C_99)=B_98 | ~r1_tarski(B_98, C_99))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_348])).
% 4.22/1.82  tff(c_371, plain, (k3_xboole_0('#skF_5', k2_struct_0('#skF_3'))='#skF_5'), inference(resolution, [status(thm)], [c_233, c_353])).
% 4.22/1.82  tff(c_20, plain, (![A_12]: (k2_subset_1(A_12)=A_12)), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.22/1.82  tff(c_22, plain, (![A_13]: (m1_subset_1(k2_subset_1(A_13), k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.22/1.82  tff(c_53, plain, (![A_13]: (m1_subset_1(A_13, k1_zfmisc_1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22])).
% 4.22/1.82  tff(c_125, plain, (![A_13, B_60]: (k9_subset_1(A_13, B_60, A_13)=k3_xboole_0(B_60, A_13))), inference(resolution, [status(thm)], [c_53, c_116])).
% 4.22/1.82  tff(c_46, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.22/1.82  tff(c_145, plain, (![A_65, B_66]: (k2_pre_topc(A_65, B_66)=k2_struct_0(A_65) | ~v1_tops_1(B_66, A_65) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.22/1.82  tff(c_148, plain, (![B_66]: (k2_pre_topc('#skF_3', B_66)=k2_struct_0('#skF_3') | ~v1_tops_1(B_66, '#skF_3') | ~m1_subset_1(B_66, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_145])).
% 4.22/1.82  tff(c_177, plain, (![B_71]: (k2_pre_topc('#skF_3', B_71)=k2_struct_0('#skF_3') | ~v1_tops_1(B_71, '#skF_3') | ~m1_subset_1(B_71, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_148])).
% 4.22/1.82  tff(c_180, plain, (k2_pre_topc('#skF_3', '#skF_4')=k2_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_78, c_177])).
% 4.22/1.82  tff(c_190, plain, (k2_pre_topc('#skF_3', '#skF_4')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_180])).
% 4.22/1.82  tff(c_52, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.22/1.82  tff(c_749, plain, (![A_127, B_128, C_129]: (k2_pre_topc(A_127, k9_subset_1(u1_struct_0(A_127), B_128, k2_pre_topc(A_127, C_129)))=k2_pre_topc(A_127, k9_subset_1(u1_struct_0(A_127), B_128, C_129)) | ~v3_pre_topc(B_128, A_127) | ~m1_subset_1(C_129, k1_zfmisc_1(u1_struct_0(A_127))) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0(A_127))) | ~l1_pre_topc(A_127) | ~v2_pre_topc(A_127))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.22/1.82  tff(c_767, plain, (![B_128, C_129]: (k2_pre_topc('#skF_3', k9_subset_1(k2_struct_0('#skF_3'), B_128, k2_pre_topc('#skF_3', C_129)))=k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), B_128, C_129)) | ~v3_pre_topc(B_128, '#skF_3') | ~m1_subset_1(C_129, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_749])).
% 4.22/1.82  tff(c_1008, plain, (![B_151, C_152]: (k2_pre_topc('#skF_3', k9_subset_1(k2_struct_0('#skF_3'), B_151, k2_pre_topc('#skF_3', C_152)))=k2_pre_topc('#skF_3', k9_subset_1(k2_struct_0('#skF_3'), B_151, C_152)) | ~v3_pre_topc(B_151, '#skF_3') | ~m1_subset_1(C_152, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(B_151, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_76, c_76, c_76, c_767])).
% 4.22/1.82  tff(c_1030, plain, (![B_151]: (k2_pre_topc('#skF_3', k9_subset_1(k2_struct_0('#skF_3'), B_151, k2_struct_0('#skF_3')))=k2_pre_topc('#skF_3', k9_subset_1(k2_struct_0('#skF_3'), B_151, '#skF_4')) | ~v3_pre_topc(B_151, '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(B_151, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_190, c_1008])).
% 4.22/1.82  tff(c_1338, plain, (![B_215]: (k2_pre_topc('#skF_3', k3_xboole_0(B_215, k2_struct_0('#skF_3')))=k2_pre_topc('#skF_3', k3_xboole_0(B_215, '#skF_4')) | ~v3_pre_topc(B_215, '#skF_3') | ~m1_subset_1(B_215, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_123, c_125, c_1030])).
% 4.22/1.82  tff(c_1344, plain, (k2_pre_topc('#skF_3', k3_xboole_0('#skF_5', k2_struct_0('#skF_3')))=k2_pre_topc('#skF_3', k3_xboole_0('#skF_5', '#skF_4')) | ~v3_pre_topc('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_77, c_1338])).
% 4.22/1.82  tff(c_1353, plain, (k2_pre_topc('#skF_3', k3_xboole_0('#skF_5', '#skF_4'))=k2_pre_topc('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_371, c_1344])).
% 4.22/1.82  tff(c_1355, plain, $false, inference(negUnitSimplification, [status(thm)], [c_135, c_1353])).
% 4.22/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.22/1.82  
% 4.22/1.82  Inference rules
% 4.22/1.82  ----------------------
% 4.22/1.82  #Ref     : 0
% 4.22/1.82  #Sup     : 314
% 4.22/1.82  #Fact    : 0
% 4.22/1.82  #Define  : 0
% 4.22/1.82  #Split   : 7
% 4.22/1.82  #Chain   : 0
% 4.22/1.82  #Close   : 0
% 4.22/1.82  
% 4.22/1.82  Ordering : KBO
% 4.22/1.82  
% 4.22/1.82  Simplification rules
% 4.22/1.82  ----------------------
% 4.22/1.82  #Subsume      : 117
% 4.22/1.82  #Demod        : 124
% 4.22/1.82  #Tautology    : 75
% 4.22/1.82  #SimpNegUnit  : 5
% 4.22/1.82  #BackRed      : 3
% 4.22/1.82  
% 4.22/1.82  #Partial instantiations: 0
% 4.22/1.82  #Strategies tried      : 1
% 4.22/1.82  
% 4.22/1.82  Timing (in seconds)
% 4.22/1.82  ----------------------
% 4.22/1.82  Preprocessing        : 0.39
% 4.22/1.82  Parsing              : 0.19
% 4.22/1.82  CNF conversion       : 0.03
% 4.22/1.82  Main loop            : 0.56
% 4.22/1.82  Inferencing          : 0.18
% 4.22/1.82  Reduction            : 0.16
% 4.22/1.82  Demodulation         : 0.11
% 4.22/1.82  BG Simplification    : 0.03
% 4.22/1.82  Subsumption          : 0.15
% 4.22/1.82  Abstraction          : 0.03
% 4.22/1.82  MUC search           : 0.00
% 4.22/1.82  Cooper               : 0.00
% 4.22/1.82  Total                : 0.98
% 4.22/1.82  Index Insertion      : 0.00
% 4.22/1.82  Index Deletion       : 0.00
% 4.22/1.82  Index Matching       : 0.00
% 4.22/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
