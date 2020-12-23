%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:53 EST 2020

% Result     : Theorem 16.74s
% Output     : CNFRefutation 16.81s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 406 expanded)
%              Number of leaves         :   29 ( 157 expanded)
%              Depth                    :   13
%              Number of atoms          :  239 (1455 expanded)
%              Number of equality atoms :   26 ( 239 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_compts_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_pre_topc > v1_compts_1 > l1_pre_topc > k1_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff(v2_compts_1,type,(
    v2_compts_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_compts_1,type,(
    v1_compts_1: $i > $o )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( B = k1_xboole_0
               => ( v2_compts_1(B,A)
                <=> v1_compts_1(k1_pre_topc(A,B)) ) )
              & ( v2_pre_topc(A)
               => ( B = k1_xboole_0
                  | ( v2_compts_1(B,A)
                  <=> v1_compts_1(k1_pre_topc(A,B)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_compts_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( ( v1_pre_topc(C)
                & m1_pre_topc(C,A) )
             => ( C = k1_pre_topc(A,B)
              <=> k2_struct_0(C) = B ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_compts_1(A)
      <=> v2_compts_1(k2_struct_0(A),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_compts_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(C,k2_struct_0(B))
               => ( v2_compts_1(C,A)
                <=> ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                     => ( D = C
                       => v2_compts_1(D,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_compts_1)).

tff(c_80,plain,
    ( v2_compts_1('#skF_3','#skF_2')
    | v1_compts_1(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_115,plain,(
    v1_compts_1(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_44,plain,
    ( ~ v1_compts_1(k1_pre_topc('#skF_2','#skF_3'))
    | ~ v2_compts_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_117,plain,(
    ~ v2_compts_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_44])).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_340,plain,(
    ! [A_76,B_77] :
      ( m1_pre_topc(k1_pre_topc(A_76,B_77),A_76)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_353,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_340])).

tff(c_359,plain,(
    m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_353])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_135,plain,(
    ! [A_62,B_63] :
      ( v1_pre_topc(k1_pre_topc(A_62,B_63))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_142,plain,
    ( v1_pre_topc(k1_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_135])).

tff(c_146,plain,(
    v1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_142])).

tff(c_633,plain,(
    ! [A_95,B_96] :
      ( k2_struct_0(k1_pre_topc(A_95,B_96)) = B_96
      | ~ m1_pre_topc(k1_pre_topc(A_95,B_96),A_95)
      | ~ v1_pre_topc(k1_pre_topc(A_95,B_96))
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_641,plain,
    ( k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3'
    | ~ v1_pre_topc(k1_pre_topc('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_359,c_633])).

tff(c_649,plain,(
    k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_146,c_641])).

tff(c_147,plain,(
    ! [A_64,B_65] :
      ( u1_struct_0(k1_pre_topc(A_64,B_65)) = B_65
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_154,plain,
    ( u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3'
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_147])).

tff(c_158,plain,(
    u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_154])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_169,plain,(
    ! [A_66,A_67] :
      ( v1_pre_topc(k1_pre_topc(A_66,A_67))
      | ~ l1_pre_topc(A_66)
      | ~ r1_tarski(A_67,u1_struct_0(A_66)) ) ),
    inference(resolution,[status(thm)],[c_10,c_135])).

tff(c_184,plain,(
    ! [A_68] :
      ( v1_pre_topc(k1_pre_topc(A_68,u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68) ) ),
    inference(resolution,[status(thm)],[c_6,c_169])).

tff(c_187,plain,
    ( v1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_3'))
    | ~ l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_184])).

tff(c_188,plain,(
    ~ l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_187])).

tff(c_189,plain,(
    ! [A_69,B_70] :
      ( m1_pre_topc(k1_pre_topc(A_69,B_70),A_69)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_196,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_189])).

tff(c_200,plain,(
    m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_196])).

tff(c_20,plain,(
    ! [B_16,A_14] :
      ( l1_pre_topc(B_16)
      | ~ m1_pre_topc(B_16,A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_203,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_200,c_20])).

tff(c_206,plain,(
    l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_203])).

tff(c_208,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_188,c_206])).

tff(c_210,plain,(
    l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_28,plain,(
    ! [A_27] :
      ( v2_compts_1(k2_struct_0(A_27),A_27)
      | ~ v1_compts_1(A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_659,plain,
    ( v2_compts_1('#skF_3',k1_pre_topc('#skF_2','#skF_3'))
    | ~ v1_compts_1(k1_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_649,c_28])).

tff(c_667,plain,(
    v2_compts_1('#skF_3',k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_115,c_659])).

tff(c_360,plain,(
    ! [C_78,A_79,B_80] :
      ( m1_subset_1(C_78,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ m1_subset_1(C_78,k1_zfmisc_1(u1_struct_0(B_80)))
      | ~ m1_pre_topc(B_80,A_79)
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_9088,plain,(
    ! [A_293,A_294,B_295] :
      ( m1_subset_1(A_293,k1_zfmisc_1(u1_struct_0(A_294)))
      | ~ m1_pre_topc(B_295,A_294)
      | ~ l1_pre_topc(A_294)
      | ~ r1_tarski(A_293,u1_struct_0(B_295)) ) ),
    inference(resolution,[status(thm)],[c_10,c_360])).

tff(c_9100,plain,(
    ! [A_293] :
      ( m1_subset_1(A_293,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_293,u1_struct_0(k1_pre_topc('#skF_2','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_359,c_9088])).

tff(c_9114,plain,(
    ! [A_293] :
      ( m1_subset_1(A_293,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski(A_293,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_40,c_9100])).

tff(c_744,plain,(
    ! [A_99,B_100,C_101] :
      ( '#skF_1'(A_99,B_100,C_101) = C_101
      | v2_compts_1(C_101,A_99)
      | ~ r1_tarski(C_101,k2_struct_0(B_100))
      | ~ m1_subset_1(C_101,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ m1_pre_topc(B_100,A_99)
      | ~ l1_pre_topc(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_10269,plain,(
    ! [A_342,B_343] :
      ( '#skF_1'(A_342,B_343,k2_struct_0(B_343)) = k2_struct_0(B_343)
      | v2_compts_1(k2_struct_0(B_343),A_342)
      | ~ m1_subset_1(k2_struct_0(B_343),k1_zfmisc_1(u1_struct_0(A_342)))
      | ~ m1_pre_topc(B_343,A_342)
      | ~ l1_pre_topc(A_342) ) ),
    inference(resolution,[status(thm)],[c_6,c_744])).

tff(c_10279,plain,(
    ! [B_343] :
      ( '#skF_1'('#skF_2',B_343,k2_struct_0(B_343)) = k2_struct_0(B_343)
      | v2_compts_1(k2_struct_0(B_343),'#skF_2')
      | ~ m1_pre_topc(B_343,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(k2_struct_0(B_343),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_9114,c_10269])).

tff(c_39344,plain,(
    ! [B_759] :
      ( '#skF_1'('#skF_2',B_759,k2_struct_0(B_759)) = k2_struct_0(B_759)
      | v2_compts_1(k2_struct_0(B_759),'#skF_2')
      | ~ m1_pre_topc(B_759,'#skF_2')
      | ~ r1_tarski(k2_struct_0(B_759),'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_10279])).

tff(c_39437,plain,
    ( k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_pre_topc('#skF_2','#skF_3'),'#skF_3')
    | v2_compts_1(k2_struct_0(k1_pre_topc('#skF_2','#skF_3')),'#skF_2')
    | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ r1_tarski(k2_struct_0(k1_pre_topc('#skF_2','#skF_3')),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_649,c_39344])).

tff(c_39499,plain,
    ( '#skF_1'('#skF_2',k1_pre_topc('#skF_2','#skF_3'),'#skF_3') = '#skF_3'
    | v2_compts_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_649,c_359,c_649,c_649,c_39437])).

tff(c_39500,plain,(
    '#skF_1'('#skF_2',k1_pre_topc('#skF_2','#skF_3'),'#skF_3') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_39499])).

tff(c_32,plain,(
    ! [A_28,B_40,C_46] :
      ( ~ v2_compts_1('#skF_1'(A_28,B_40,C_46),B_40)
      | v2_compts_1(C_46,A_28)
      | ~ r1_tarski(C_46,k2_struct_0(B_40))
      | ~ m1_subset_1(C_46,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ m1_pre_topc(B_40,A_28)
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_39610,plain,
    ( ~ v2_compts_1('#skF_3',k1_pre_topc('#skF_2','#skF_3'))
    | v2_compts_1('#skF_3','#skF_2')
    | ~ r1_tarski('#skF_3',k2_struct_0(k1_pre_topc('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_39500,c_32])).

tff(c_39722,plain,(
    v2_compts_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_359,c_38,c_6,c_649,c_667,c_39610])).

tff(c_39724,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_39722])).

tff(c_39726,plain,(
    ~ v1_compts_1(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_39771,plain,(
    ! [A_769,B_770] :
      ( m1_pre_topc(k1_pre_topc(A_769,B_770),A_769)
      | ~ m1_subset_1(B_770,k1_zfmisc_1(u1_struct_0(A_769)))
      | ~ l1_pre_topc(A_769) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_39776,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_39771])).

tff(c_39780,plain,(
    m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_39776])).

tff(c_39783,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_39780,c_20])).

tff(c_39786,plain,(
    l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_39783])).

tff(c_39746,plain,(
    ! [A_764,B_765] :
      ( v1_pre_topc(k1_pre_topc(A_764,B_765))
      | ~ m1_subset_1(B_765,k1_zfmisc_1(u1_struct_0(A_764)))
      | ~ l1_pre_topc(A_764) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_39753,plain,
    ( v1_pre_topc(k1_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_39746])).

tff(c_39757,plain,(
    v1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_39753])).

tff(c_40420,plain,(
    ! [A_797,B_798] :
      ( k2_struct_0(k1_pre_topc(A_797,B_798)) = B_798
      | ~ m1_pre_topc(k1_pre_topc(A_797,B_798),A_797)
      | ~ v1_pre_topc(k1_pre_topc(A_797,B_798))
      | ~ m1_subset_1(B_798,k1_zfmisc_1(u1_struct_0(A_797)))
      | ~ l1_pre_topc(A_797) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_40428,plain,
    ( k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3'
    | ~ v1_pre_topc(k1_pre_topc('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_39780,c_40420])).

tff(c_40436,plain,(
    k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_39757,c_40428])).

tff(c_26,plain,(
    ! [A_27] :
      ( v1_compts_1(A_27)
      | ~ v2_compts_1(k2_struct_0(A_27),A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_40446,plain,
    ( v1_compts_1(k1_pre_topc('#skF_2','#skF_3'))
    | ~ v2_compts_1('#skF_3',k1_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_40436,c_26])).

tff(c_40454,plain,
    ( v1_compts_1(k1_pre_topc('#skF_2','#skF_3'))
    | ~ v2_compts_1('#skF_3',k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39786,c_40446])).

tff(c_40455,plain,(
    ~ v2_compts_1('#skF_3',k1_pre_topc('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_39726,c_40454])).

tff(c_39803,plain,(
    ! [A_775,B_776] :
      ( u1_struct_0(k1_pre_topc(A_775,B_776)) = B_776
      | ~ m1_subset_1(B_776,k1_zfmisc_1(u1_struct_0(A_775)))
      | ~ l1_pre_topc(A_775) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_39810,plain,
    ( u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3'
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_39803])).

tff(c_39814,plain,(
    u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_39810])).

tff(c_39725,plain,(
    v2_compts_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_40908,plain,(
    ! [D_816,B_817,A_818] :
      ( v2_compts_1(D_816,B_817)
      | ~ m1_subset_1(D_816,k1_zfmisc_1(u1_struct_0(B_817)))
      | ~ v2_compts_1(D_816,A_818)
      | ~ r1_tarski(D_816,k2_struct_0(B_817))
      | ~ m1_subset_1(D_816,k1_zfmisc_1(u1_struct_0(A_818)))
      | ~ m1_pre_topc(B_817,A_818)
      | ~ l1_pre_topc(A_818) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_42649,plain,(
    ! [A_864,B_865,A_866] :
      ( v2_compts_1(A_864,B_865)
      | ~ v2_compts_1(A_864,A_866)
      | ~ r1_tarski(A_864,k2_struct_0(B_865))
      | ~ m1_subset_1(A_864,k1_zfmisc_1(u1_struct_0(A_866)))
      | ~ m1_pre_topc(B_865,A_866)
      | ~ l1_pre_topc(A_866)
      | ~ r1_tarski(A_864,u1_struct_0(B_865)) ) ),
    inference(resolution,[status(thm)],[c_10,c_40908])).

tff(c_42695,plain,(
    ! [B_865] :
      ( v2_compts_1('#skF_3',B_865)
      | ~ v2_compts_1('#skF_3','#skF_2')
      | ~ r1_tarski('#skF_3',k2_struct_0(B_865))
      | ~ m1_pre_topc(B_865,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski('#skF_3',u1_struct_0(B_865)) ) ),
    inference(resolution,[status(thm)],[c_38,c_42649])).

tff(c_42892,plain,(
    ! [B_871] :
      ( v2_compts_1('#skF_3',B_871)
      | ~ r1_tarski('#skF_3',k2_struct_0(B_871))
      | ~ m1_pre_topc(B_871,'#skF_2')
      | ~ r1_tarski('#skF_3',u1_struct_0(B_871)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_39725,c_42695])).

tff(c_42942,plain,
    ( v2_compts_1('#skF_3',k1_pre_topc('#skF_2','#skF_3'))
    | ~ r1_tarski('#skF_3',k2_struct_0(k1_pre_topc('#skF_2','#skF_3')))
    | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_39814,c_42892])).

tff(c_42965,plain,(
    v2_compts_1('#skF_3',k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_39780,c_6,c_40436,c_42942])).

tff(c_42967,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40455,c_42965])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:22:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.74/8.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.74/8.66  
% 16.74/8.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.74/8.66  %$ v2_compts_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_pre_topc > v1_compts_1 > l1_pre_topc > k1_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 16.74/8.66  
% 16.74/8.66  %Foreground sorts:
% 16.74/8.66  
% 16.74/8.66  
% 16.74/8.66  %Background operators:
% 16.74/8.66  
% 16.74/8.66  
% 16.74/8.66  %Foreground operators:
% 16.74/8.66  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 16.74/8.66  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 16.74/8.66  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 16.74/8.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.74/8.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.74/8.66  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 16.74/8.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.74/8.66  tff('#skF_2', type, '#skF_2': $i).
% 16.74/8.66  tff('#skF_3', type, '#skF_3': $i).
% 16.74/8.66  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 16.74/8.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.74/8.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.74/8.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.74/8.66  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 16.74/8.66  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 16.74/8.66  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 16.74/8.66  tff(v1_compts_1, type, v1_compts_1: $i > $o).
% 16.74/8.66  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 16.74/8.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.74/8.66  
% 16.81/8.67  tff(f_126, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (((B = k1_xboole_0) => (v2_compts_1(B, A) <=> v1_compts_1(k1_pre_topc(A, B)))) & (v2_pre_topc(A) => ((B = k1_xboole_0) | (v2_compts_1(B, A) <=> v1_compts_1(k1_pre_topc(A, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_compts_1)).
% 16.81/8.67  tff(f_57, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 16.81/8.67  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 16.81/8.67  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((v1_pre_topc(C) & m1_pre_topc(C, A)) => ((C = k1_pre_topc(A, B)) <=> (k2_struct_0(C) = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_pre_topc)).
% 16.81/8.67  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_pre_topc)).
% 16.81/8.67  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 16.81/8.67  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 16.81/8.67  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (v1_compts_1(A) <=> v2_compts_1(k2_struct_0(A), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_compts_1)).
% 16.81/8.67  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 16.81/8.67  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, k2_struct_0(B)) => (v2_compts_1(C, A) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((D = C) => v2_compts_1(D, B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_compts_1)).
% 16.81/8.67  tff(c_80, plain, (v2_compts_1('#skF_3', '#skF_2') | v1_compts_1(k1_pre_topc('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 16.81/8.67  tff(c_115, plain, (v1_compts_1(k1_pre_topc('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_80])).
% 16.81/8.67  tff(c_44, plain, (~v1_compts_1(k1_pre_topc('#skF_2', '#skF_3')) | ~v2_compts_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 16.81/8.67  tff(c_117, plain, (~v2_compts_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_115, c_44])).
% 16.81/8.67  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 16.81/8.67  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 16.81/8.68  tff(c_340, plain, (![A_76, B_77]: (m1_pre_topc(k1_pre_topc(A_76, B_77), A_76) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_57])).
% 16.81/8.68  tff(c_353, plain, (m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_340])).
% 16.81/8.68  tff(c_359, plain, (m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_353])).
% 16.81/8.68  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.81/8.68  tff(c_135, plain, (![A_62, B_63]: (v1_pre_topc(k1_pre_topc(A_62, B_63)) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_57])).
% 16.81/8.68  tff(c_142, plain, (v1_pre_topc(k1_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_135])).
% 16.81/8.68  tff(c_146, plain, (v1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_142])).
% 16.81/8.68  tff(c_633, plain, (![A_95, B_96]: (k2_struct_0(k1_pre_topc(A_95, B_96))=B_96 | ~m1_pre_topc(k1_pre_topc(A_95, B_96), A_95) | ~v1_pre_topc(k1_pre_topc(A_95, B_96)) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_49])).
% 16.81/8.68  tff(c_641, plain, (k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3' | ~v1_pre_topc(k1_pre_topc('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_359, c_633])).
% 16.81/8.68  tff(c_649, plain, (k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_146, c_641])).
% 16.81/8.68  tff(c_147, plain, (![A_64, B_65]: (u1_struct_0(k1_pre_topc(A_64, B_65))=B_65 | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_71])).
% 16.81/8.68  tff(c_154, plain, (u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3' | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_147])).
% 16.81/8.68  tff(c_158, plain, (u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_154])).
% 16.81/8.68  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 16.81/8.68  tff(c_169, plain, (![A_66, A_67]: (v1_pre_topc(k1_pre_topc(A_66, A_67)) | ~l1_pre_topc(A_66) | ~r1_tarski(A_67, u1_struct_0(A_66)))), inference(resolution, [status(thm)], [c_10, c_135])).
% 16.81/8.68  tff(c_184, plain, (![A_68]: (v1_pre_topc(k1_pre_topc(A_68, u1_struct_0(A_68))) | ~l1_pre_topc(A_68))), inference(resolution, [status(thm)], [c_6, c_169])).
% 16.81/8.68  tff(c_187, plain, (v1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_3')) | ~l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_158, c_184])).
% 16.81/8.68  tff(c_188, plain, (~l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_187])).
% 16.81/8.68  tff(c_189, plain, (![A_69, B_70]: (m1_pre_topc(k1_pre_topc(A_69, B_70), A_69) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_57])).
% 16.81/8.68  tff(c_196, plain, (m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_189])).
% 16.81/8.68  tff(c_200, plain, (m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_196])).
% 16.81/8.68  tff(c_20, plain, (![B_16, A_14]: (l1_pre_topc(B_16) | ~m1_pre_topc(B_16, A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 16.81/8.68  tff(c_203, plain, (l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_200, c_20])).
% 16.81/8.68  tff(c_206, plain, (l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_203])).
% 16.81/8.68  tff(c_208, plain, $false, inference(negUnitSimplification, [status(thm)], [c_188, c_206])).
% 16.81/8.68  tff(c_210, plain, (l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_187])).
% 16.81/8.68  tff(c_28, plain, (![A_27]: (v2_compts_1(k2_struct_0(A_27), A_27) | ~v1_compts_1(A_27) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_87])).
% 16.81/8.68  tff(c_659, plain, (v2_compts_1('#skF_3', k1_pre_topc('#skF_2', '#skF_3')) | ~v1_compts_1(k1_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_649, c_28])).
% 16.81/8.68  tff(c_667, plain, (v2_compts_1('#skF_3', k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_115, c_659])).
% 16.81/8.68  tff(c_360, plain, (![C_78, A_79, B_80]: (m1_subset_1(C_78, k1_zfmisc_1(u1_struct_0(A_79))) | ~m1_subset_1(C_78, k1_zfmisc_1(u1_struct_0(B_80))) | ~m1_pre_topc(B_80, A_79) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_81])).
% 16.81/8.68  tff(c_9088, plain, (![A_293, A_294, B_295]: (m1_subset_1(A_293, k1_zfmisc_1(u1_struct_0(A_294))) | ~m1_pre_topc(B_295, A_294) | ~l1_pre_topc(A_294) | ~r1_tarski(A_293, u1_struct_0(B_295)))), inference(resolution, [status(thm)], [c_10, c_360])).
% 16.81/8.68  tff(c_9100, plain, (![A_293]: (m1_subset_1(A_293, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_293, u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_359, c_9088])).
% 16.81/8.68  tff(c_9114, plain, (![A_293]: (m1_subset_1(A_293, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski(A_293, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_40, c_9100])).
% 16.81/8.68  tff(c_744, plain, (![A_99, B_100, C_101]: ('#skF_1'(A_99, B_100, C_101)=C_101 | v2_compts_1(C_101, A_99) | ~r1_tarski(C_101, k2_struct_0(B_100)) | ~m1_subset_1(C_101, k1_zfmisc_1(u1_struct_0(A_99))) | ~m1_pre_topc(B_100, A_99) | ~l1_pre_topc(A_99))), inference(cnfTransformation, [status(thm)], [f_106])).
% 16.81/8.68  tff(c_10269, plain, (![A_342, B_343]: ('#skF_1'(A_342, B_343, k2_struct_0(B_343))=k2_struct_0(B_343) | v2_compts_1(k2_struct_0(B_343), A_342) | ~m1_subset_1(k2_struct_0(B_343), k1_zfmisc_1(u1_struct_0(A_342))) | ~m1_pre_topc(B_343, A_342) | ~l1_pre_topc(A_342))), inference(resolution, [status(thm)], [c_6, c_744])).
% 16.81/8.68  tff(c_10279, plain, (![B_343]: ('#skF_1'('#skF_2', B_343, k2_struct_0(B_343))=k2_struct_0(B_343) | v2_compts_1(k2_struct_0(B_343), '#skF_2') | ~m1_pre_topc(B_343, '#skF_2') | ~l1_pre_topc('#skF_2') | ~r1_tarski(k2_struct_0(B_343), '#skF_3'))), inference(resolution, [status(thm)], [c_9114, c_10269])).
% 16.81/8.68  tff(c_39344, plain, (![B_759]: ('#skF_1'('#skF_2', B_759, k2_struct_0(B_759))=k2_struct_0(B_759) | v2_compts_1(k2_struct_0(B_759), '#skF_2') | ~m1_pre_topc(B_759, '#skF_2') | ~r1_tarski(k2_struct_0(B_759), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_10279])).
% 16.81/8.68  tff(c_39437, plain, (k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_pre_topc('#skF_2', '#skF_3'), '#skF_3') | v2_compts_1(k2_struct_0(k1_pre_topc('#skF_2', '#skF_3')), '#skF_2') | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~r1_tarski(k2_struct_0(k1_pre_topc('#skF_2', '#skF_3')), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_649, c_39344])).
% 16.81/8.68  tff(c_39499, plain, ('#skF_1'('#skF_2', k1_pre_topc('#skF_2', '#skF_3'), '#skF_3')='#skF_3' | v2_compts_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_649, c_359, c_649, c_649, c_39437])).
% 16.81/8.68  tff(c_39500, plain, ('#skF_1'('#skF_2', k1_pre_topc('#skF_2', '#skF_3'), '#skF_3')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_117, c_39499])).
% 16.81/8.68  tff(c_32, plain, (![A_28, B_40, C_46]: (~v2_compts_1('#skF_1'(A_28, B_40, C_46), B_40) | v2_compts_1(C_46, A_28) | ~r1_tarski(C_46, k2_struct_0(B_40)) | ~m1_subset_1(C_46, k1_zfmisc_1(u1_struct_0(A_28))) | ~m1_pre_topc(B_40, A_28) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_106])).
% 16.81/8.68  tff(c_39610, plain, (~v2_compts_1('#skF_3', k1_pre_topc('#skF_2', '#skF_3')) | v2_compts_1('#skF_3', '#skF_2') | ~r1_tarski('#skF_3', k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_39500, c_32])).
% 16.81/8.68  tff(c_39722, plain, (v2_compts_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_359, c_38, c_6, c_649, c_667, c_39610])).
% 16.81/8.68  tff(c_39724, plain, $false, inference(negUnitSimplification, [status(thm)], [c_117, c_39722])).
% 16.81/8.68  tff(c_39726, plain, (~v1_compts_1(k1_pre_topc('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_80])).
% 16.81/8.68  tff(c_39771, plain, (![A_769, B_770]: (m1_pre_topc(k1_pre_topc(A_769, B_770), A_769) | ~m1_subset_1(B_770, k1_zfmisc_1(u1_struct_0(A_769))) | ~l1_pre_topc(A_769))), inference(cnfTransformation, [status(thm)], [f_57])).
% 16.81/8.68  tff(c_39776, plain, (m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_39771])).
% 16.81/8.68  tff(c_39780, plain, (m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_39776])).
% 16.81/8.68  tff(c_39783, plain, (l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_39780, c_20])).
% 16.81/8.68  tff(c_39786, plain, (l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_39783])).
% 16.81/8.68  tff(c_39746, plain, (![A_764, B_765]: (v1_pre_topc(k1_pre_topc(A_764, B_765)) | ~m1_subset_1(B_765, k1_zfmisc_1(u1_struct_0(A_764))) | ~l1_pre_topc(A_764))), inference(cnfTransformation, [status(thm)], [f_57])).
% 16.81/8.68  tff(c_39753, plain, (v1_pre_topc(k1_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_39746])).
% 16.81/8.68  tff(c_39757, plain, (v1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_39753])).
% 16.81/8.68  tff(c_40420, plain, (![A_797, B_798]: (k2_struct_0(k1_pre_topc(A_797, B_798))=B_798 | ~m1_pre_topc(k1_pre_topc(A_797, B_798), A_797) | ~v1_pre_topc(k1_pre_topc(A_797, B_798)) | ~m1_subset_1(B_798, k1_zfmisc_1(u1_struct_0(A_797))) | ~l1_pre_topc(A_797))), inference(cnfTransformation, [status(thm)], [f_49])).
% 16.81/8.68  tff(c_40428, plain, (k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3' | ~v1_pre_topc(k1_pre_topc('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_39780, c_40420])).
% 16.81/8.68  tff(c_40436, plain, (k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_39757, c_40428])).
% 16.81/8.68  tff(c_26, plain, (![A_27]: (v1_compts_1(A_27) | ~v2_compts_1(k2_struct_0(A_27), A_27) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_87])).
% 16.81/8.68  tff(c_40446, plain, (v1_compts_1(k1_pre_topc('#skF_2', '#skF_3')) | ~v2_compts_1('#skF_3', k1_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_40436, c_26])).
% 16.81/8.68  tff(c_40454, plain, (v1_compts_1(k1_pre_topc('#skF_2', '#skF_3')) | ~v2_compts_1('#skF_3', k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_39786, c_40446])).
% 16.81/8.68  tff(c_40455, plain, (~v2_compts_1('#skF_3', k1_pre_topc('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_39726, c_40454])).
% 16.81/8.68  tff(c_39803, plain, (![A_775, B_776]: (u1_struct_0(k1_pre_topc(A_775, B_776))=B_776 | ~m1_subset_1(B_776, k1_zfmisc_1(u1_struct_0(A_775))) | ~l1_pre_topc(A_775))), inference(cnfTransformation, [status(thm)], [f_71])).
% 16.81/8.68  tff(c_39810, plain, (u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3' | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_39803])).
% 16.81/8.68  tff(c_39814, plain, (u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_39810])).
% 16.81/8.68  tff(c_39725, plain, (v2_compts_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_80])).
% 16.81/8.68  tff(c_40908, plain, (![D_816, B_817, A_818]: (v2_compts_1(D_816, B_817) | ~m1_subset_1(D_816, k1_zfmisc_1(u1_struct_0(B_817))) | ~v2_compts_1(D_816, A_818) | ~r1_tarski(D_816, k2_struct_0(B_817)) | ~m1_subset_1(D_816, k1_zfmisc_1(u1_struct_0(A_818))) | ~m1_pre_topc(B_817, A_818) | ~l1_pre_topc(A_818))), inference(cnfTransformation, [status(thm)], [f_106])).
% 16.81/8.68  tff(c_42649, plain, (![A_864, B_865, A_866]: (v2_compts_1(A_864, B_865) | ~v2_compts_1(A_864, A_866) | ~r1_tarski(A_864, k2_struct_0(B_865)) | ~m1_subset_1(A_864, k1_zfmisc_1(u1_struct_0(A_866))) | ~m1_pre_topc(B_865, A_866) | ~l1_pre_topc(A_866) | ~r1_tarski(A_864, u1_struct_0(B_865)))), inference(resolution, [status(thm)], [c_10, c_40908])).
% 16.81/8.68  tff(c_42695, plain, (![B_865]: (v2_compts_1('#skF_3', B_865) | ~v2_compts_1('#skF_3', '#skF_2') | ~r1_tarski('#skF_3', k2_struct_0(B_865)) | ~m1_pre_topc(B_865, '#skF_2') | ~l1_pre_topc('#skF_2') | ~r1_tarski('#skF_3', u1_struct_0(B_865)))), inference(resolution, [status(thm)], [c_38, c_42649])).
% 16.81/8.68  tff(c_42892, plain, (![B_871]: (v2_compts_1('#skF_3', B_871) | ~r1_tarski('#skF_3', k2_struct_0(B_871)) | ~m1_pre_topc(B_871, '#skF_2') | ~r1_tarski('#skF_3', u1_struct_0(B_871)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_39725, c_42695])).
% 16.81/8.68  tff(c_42942, plain, (v2_compts_1('#skF_3', k1_pre_topc('#skF_2', '#skF_3')) | ~r1_tarski('#skF_3', k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))) | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~r1_tarski('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_39814, c_42892])).
% 16.81/8.68  tff(c_42965, plain, (v2_compts_1('#skF_3', k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_39780, c_6, c_40436, c_42942])).
% 16.81/8.68  tff(c_42967, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40455, c_42965])).
% 16.81/8.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.81/8.68  
% 16.81/8.68  Inference rules
% 16.81/8.68  ----------------------
% 16.81/8.68  #Ref     : 0
% 16.81/8.68  #Sup     : 10406
% 16.81/8.68  #Fact    : 0
% 16.81/8.68  #Define  : 0
% 16.81/8.68  #Split   : 26
% 16.81/8.68  #Chain   : 0
% 16.81/8.68  #Close   : 0
% 16.81/8.68  
% 16.81/8.68  Ordering : KBO
% 16.81/8.68  
% 16.81/8.68  Simplification rules
% 16.81/8.68  ----------------------
% 16.81/8.68  #Subsume      : 2239
% 16.81/8.68  #Demod        : 10009
% 16.81/8.68  #Tautology    : 1726
% 16.81/8.68  #SimpNegUnit  : 90
% 16.81/8.68  #BackRed      : 16
% 16.81/8.68  
% 16.81/8.68  #Partial instantiations: 0
% 16.81/8.68  #Strategies tried      : 1
% 16.81/8.68  
% 16.81/8.68  Timing (in seconds)
% 16.81/8.68  ----------------------
% 16.81/8.68  Preprocessing        : 0.35
% 16.81/8.68  Parsing              : 0.18
% 16.81/8.68  CNF conversion       : 0.03
% 16.81/8.68  Main loop            : 7.48
% 16.81/8.68  Inferencing          : 1.32
% 16.81/8.68  Reduction            : 1.92
% 16.81/8.68  Demodulation         : 1.37
% 16.81/8.68  BG Simplification    : 0.17
% 16.81/8.68  Subsumption          : 3.72
% 16.81/8.68  Abstraction          : 0.22
% 16.81/8.68  MUC search           : 0.00
% 16.81/8.68  Cooper               : 0.00
% 16.81/8.68  Total                : 7.86
% 16.81/8.68  Index Insertion      : 0.00
% 16.81/8.68  Index Deletion       : 0.00
% 16.81/8.68  Index Matching       : 0.00
% 16.81/8.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
