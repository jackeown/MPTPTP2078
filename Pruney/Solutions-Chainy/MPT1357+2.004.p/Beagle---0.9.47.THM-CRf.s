%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:53 EST 2020

% Result     : Theorem 10.68s
% Output     : CNFRefutation 10.68s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 840 expanded)
%              Number of leaves         :   30 ( 297 expanded)
%              Depth                    :   16
%              Number of atoms          :  218 (2385 expanded)
%              Number of equality atoms :   30 ( 534 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_compts_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_pre_topc > v1_compts_1 > l1_struct_0 > l1_pre_topc > k1_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(f_120,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_compts_1)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_compts_1(A)
      <=> v2_compts_1(k2_struct_0(A),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_compts_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_100,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_compts_1)).

tff(c_80,plain,
    ( v2_compts_1('#skF_3','#skF_2')
    | v1_compts_1(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_120,plain,(
    v1_compts_1(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_44,plain,
    ( ~ v1_compts_1(k1_pre_topc('#skF_2','#skF_3'))
    | ~ v2_compts_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_133,plain,(
    ~ v2_compts_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_44])).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_18,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_105,plain,(
    ! [A_48] :
      ( u1_struct_0(A_48) = k2_struct_0(A_48)
      | ~ l1_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_110,plain,(
    ! [A_49] :
      ( u1_struct_0(A_49) = k2_struct_0(A_49)
      | ~ l1_pre_topc(A_49) ) ),
    inference(resolution,[status(thm)],[c_18,c_105])).

tff(c_114,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_110])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_115,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_38])).

tff(c_172,plain,(
    ! [A_63,B_64] :
      ( m1_pre_topc(k1_pre_topc(A_63,B_64),A_63)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_177,plain,(
    ! [B_64] :
      ( m1_pre_topc(k1_pre_topc('#skF_2',B_64),'#skF_2')
      | ~ m1_subset_1(B_64,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_172])).

tff(c_203,plain,(
    ! [B_68] :
      ( m1_pre_topc(k1_pre_topc('#skF_2',B_68),'#skF_2')
      | ~ m1_subset_1(B_68,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_177])).

tff(c_212,plain,(
    m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_115,c_203])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_263,plain,(
    ! [A_71,B_72] :
      ( u1_struct_0(k1_pre_topc(A_71,B_72)) = B_72
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_273,plain,(
    ! [B_72] :
      ( u1_struct_0(k1_pre_topc('#skF_2',B_72)) = B_72
      | ~ m1_subset_1(B_72,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_263])).

tff(c_289,plain,(
    ! [B_73] :
      ( u1_struct_0(k1_pre_topc('#skF_2',B_73)) = B_73
      | ~ m1_subset_1(B_73,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_273])).

tff(c_298,plain,(
    u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_115,c_289])).

tff(c_20,plain,(
    ! [B_11,A_9] :
      ( l1_pre_topc(B_11)
      | ~ m1_pre_topc(B_11,A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_215,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_212,c_20])).

tff(c_218,plain,(
    l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_215])).

tff(c_109,plain,(
    ! [A_8] :
      ( u1_struct_0(A_8) = k2_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(resolution,[status(thm)],[c_18,c_105])).

tff(c_222,plain,(
    u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) = k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_218,c_109])).

tff(c_299,plain,(
    k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_222])).

tff(c_28,plain,(
    ! [A_22] :
      ( v2_compts_1(k2_struct_0(A_22),A_22)
      | ~ v1_compts_1(A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_332,plain,
    ( v2_compts_1('#skF_3',k1_pre_topc('#skF_2','#skF_3'))
    | ~ v1_compts_1(k1_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_28])).

tff(c_339,plain,(
    v2_compts_1('#skF_3',k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_120,c_332])).

tff(c_123,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(A_54,B_55)
      | ~ m1_subset_1(A_54,k1_zfmisc_1(B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_131,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_115,c_123])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_518,plain,(
    ! [A_85,B_86,C_87] :
      ( '#skF_1'(A_85,B_86,C_87) = C_87
      | v2_compts_1(C_87,A_85)
      | ~ r1_tarski(C_87,k2_struct_0(B_86))
      | ~ m1_subset_1(C_87,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ m1_pre_topc(B_86,A_85)
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1784,plain,(
    ! [A_135,B_136] :
      ( '#skF_1'(A_135,B_136,k2_struct_0(B_136)) = k2_struct_0(B_136)
      | v2_compts_1(k2_struct_0(B_136),A_135)
      | ~ m1_subset_1(k2_struct_0(B_136),k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ m1_pre_topc(B_136,A_135)
      | ~ l1_pre_topc(A_135) ) ),
    inference(resolution,[status(thm)],[c_6,c_518])).

tff(c_4761,plain,(
    ! [A_214,B_215] :
      ( '#skF_1'(A_214,B_215,k2_struct_0(B_215)) = k2_struct_0(B_215)
      | v2_compts_1(k2_struct_0(B_215),A_214)
      | ~ m1_pre_topc(B_215,A_214)
      | ~ l1_pre_topc(A_214)
      | ~ r1_tarski(k2_struct_0(B_215),u1_struct_0(A_214)) ) ),
    inference(resolution,[status(thm)],[c_10,c_1784])).

tff(c_4822,plain,(
    ! [B_215] :
      ( '#skF_1'('#skF_2',B_215,k2_struct_0(B_215)) = k2_struct_0(B_215)
      | v2_compts_1(k2_struct_0(B_215),'#skF_2')
      | ~ m1_pre_topc(B_215,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(k2_struct_0(B_215),k2_struct_0('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_4761])).

tff(c_5606,plain,(
    ! [B_226] :
      ( '#skF_1'('#skF_2',B_226,k2_struct_0(B_226)) = k2_struct_0(B_226)
      | v2_compts_1(k2_struct_0(B_226),'#skF_2')
      | ~ m1_pre_topc(B_226,'#skF_2')
      | ~ r1_tarski(k2_struct_0(B_226),k2_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4822])).

tff(c_5630,plain,
    ( '#skF_1'('#skF_2',k1_pre_topc('#skF_2','#skF_3'),k2_struct_0(k1_pre_topc('#skF_2','#skF_3'))) = k2_struct_0(k1_pre_topc('#skF_2','#skF_3'))
    | v2_compts_1(k2_struct_0(k1_pre_topc('#skF_2','#skF_3')),'#skF_2')
    | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ r1_tarski('#skF_3',k2_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_5606])).

tff(c_5651,plain,
    ( '#skF_1'('#skF_2',k1_pre_topc('#skF_2','#skF_3'),'#skF_3') = '#skF_3'
    | v2_compts_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_212,c_299,c_299,c_299,c_5630])).

tff(c_5652,plain,(
    '#skF_1'('#skF_2',k1_pre_topc('#skF_2','#skF_3'),'#skF_3') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_5651])).

tff(c_32,plain,(
    ! [A_23,B_35,C_41] :
      ( ~ v2_compts_1('#skF_1'(A_23,B_35,C_41),B_35)
      | v2_compts_1(C_41,A_23)
      | ~ r1_tarski(C_41,k2_struct_0(B_35))
      | ~ m1_subset_1(C_41,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ m1_pre_topc(B_35,A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_5667,plain,
    ( ~ v2_compts_1('#skF_3',k1_pre_topc('#skF_2','#skF_3'))
    | v2_compts_1('#skF_3','#skF_2')
    | ~ r1_tarski('#skF_3',k2_struct_0(k1_pre_topc('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5652,c_32])).

tff(c_5683,plain,(
    v2_compts_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_212,c_115,c_114,c_6,c_299,c_339,c_5667])).

tff(c_5685,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_5683])).

tff(c_5687,plain,(
    ~ v1_compts_1(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_5729,plain,(
    ! [A_239,B_240] :
      ( m1_pre_topc(k1_pre_topc(A_239,B_240),A_239)
      | ~ m1_subset_1(B_240,k1_zfmisc_1(u1_struct_0(A_239)))
      | ~ l1_pre_topc(A_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_5734,plain,(
    ! [B_240] :
      ( m1_pre_topc(k1_pre_topc('#skF_2',B_240),'#skF_2')
      | ~ m1_subset_1(B_240,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_5729])).

tff(c_5759,plain,(
    ! [B_243] :
      ( m1_pre_topc(k1_pre_topc('#skF_2',B_243),'#skF_2')
      | ~ m1_subset_1(B_243,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5734])).

tff(c_5768,plain,(
    m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_115,c_5759])).

tff(c_5771,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_5768,c_20])).

tff(c_5774,plain,(
    l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5771])).

tff(c_5803,plain,(
    ! [A_245,B_246] :
      ( u1_struct_0(k1_pre_topc(A_245,B_246)) = B_246
      | ~ m1_subset_1(B_246,k1_zfmisc_1(u1_struct_0(A_245)))
      | ~ l1_pre_topc(A_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_5813,plain,(
    ! [B_246] :
      ( u1_struct_0(k1_pre_topc('#skF_2',B_246)) = B_246
      | ~ m1_subset_1(B_246,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_5803])).

tff(c_5845,plain,(
    ! [B_249] :
      ( u1_struct_0(k1_pre_topc('#skF_2',B_249)) = B_249
      | ~ m1_subset_1(B_249,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5813])).

tff(c_5854,plain,(
    u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_115,c_5845])).

tff(c_5778,plain,(
    u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) = k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_5774,c_109])).

tff(c_5855,plain,(
    k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5854,c_5778])).

tff(c_26,plain,(
    ! [A_22] :
      ( v1_compts_1(A_22)
      | ~ v2_compts_1(k2_struct_0(A_22),A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_5882,plain,
    ( v1_compts_1(k1_pre_topc('#skF_2','#skF_3'))
    | ~ v2_compts_1('#skF_3',k1_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5855,c_26])).

tff(c_5889,plain,
    ( v1_compts_1(k1_pre_topc('#skF_2','#skF_3'))
    | ~ v2_compts_1('#skF_3',k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5774,c_5882])).

tff(c_5890,plain,(
    ~ v2_compts_1('#skF_3',k1_pre_topc('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_5687,c_5889])).

tff(c_5686,plain,(
    v2_compts_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_6867,plain,(
    ! [D_293,B_294,A_295] :
      ( v2_compts_1(D_293,B_294)
      | ~ m1_subset_1(D_293,k1_zfmisc_1(u1_struct_0(B_294)))
      | ~ v2_compts_1(D_293,A_295)
      | ~ r1_tarski(D_293,k2_struct_0(B_294))
      | ~ m1_subset_1(D_293,k1_zfmisc_1(u1_struct_0(A_295)))
      | ~ m1_pre_topc(B_294,A_295)
      | ~ l1_pre_topc(A_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_7981,plain,(
    ! [A_336,B_337,A_338] :
      ( v2_compts_1(A_336,B_337)
      | ~ v2_compts_1(A_336,A_338)
      | ~ r1_tarski(A_336,k2_struct_0(B_337))
      | ~ m1_subset_1(A_336,k1_zfmisc_1(u1_struct_0(A_338)))
      | ~ m1_pre_topc(B_337,A_338)
      | ~ l1_pre_topc(A_338)
      | ~ r1_tarski(A_336,u1_struct_0(B_337)) ) ),
    inference(resolution,[status(thm)],[c_10,c_6867])).

tff(c_8016,plain,(
    ! [A_336,B_337] :
      ( v2_compts_1(A_336,B_337)
      | ~ v2_compts_1(A_336,'#skF_2')
      | ~ r1_tarski(A_336,k2_struct_0(B_337))
      | ~ m1_subset_1(A_336,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_337,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_336,u1_struct_0(B_337)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_7981])).

tff(c_17443,plain,(
    ! [A_502,B_503] :
      ( v2_compts_1(A_502,B_503)
      | ~ v2_compts_1(A_502,'#skF_2')
      | ~ r1_tarski(A_502,k2_struct_0(B_503))
      | ~ m1_subset_1(A_502,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_503,'#skF_2')
      | ~ r1_tarski(A_502,u1_struct_0(B_503)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_8016])).

tff(c_17461,plain,(
    ! [B_503] :
      ( v2_compts_1('#skF_3',B_503)
      | ~ v2_compts_1('#skF_3','#skF_2')
      | ~ r1_tarski('#skF_3',k2_struct_0(B_503))
      | ~ m1_pre_topc(B_503,'#skF_2')
      | ~ r1_tarski('#skF_3',u1_struct_0(B_503)) ) ),
    inference(resolution,[status(thm)],[c_115,c_17443])).

tff(c_17474,plain,(
    ! [B_504] :
      ( v2_compts_1('#skF_3',B_504)
      | ~ r1_tarski('#skF_3',k2_struct_0(B_504))
      | ~ m1_pre_topc(B_504,'#skF_2')
      | ~ r1_tarski('#skF_3',u1_struct_0(B_504)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5686,c_17461])).

tff(c_17558,plain,
    ( v2_compts_1('#skF_3',k1_pre_topc('#skF_2','#skF_3'))
    | ~ r1_tarski('#skF_3',k2_struct_0(k1_pre_topc('#skF_2','#skF_3')))
    | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5854,c_17474])).

tff(c_17593,plain,(
    v2_compts_1('#skF_3',k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5768,c_6,c_5855,c_17558])).

tff(c_17595,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5890,c_17593])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.09  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.09/0.28  % Computer   : n022.cluster.edu
% 0.09/0.28  % Model      : x86_64 x86_64
% 0.09/0.28  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.28  % Memory     : 8042.1875MB
% 0.09/0.28  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.28  % CPULimit   : 60
% 0.09/0.28  % DateTime   : Tue Dec  1 14:19:25 EST 2020
% 0.09/0.28  % CPUTime    : 
% 0.09/0.29  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.68/3.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.68/3.99  
% 10.68/3.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.68/3.99  %$ v2_compts_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_pre_topc > v1_compts_1 > l1_struct_0 > l1_pre_topc > k1_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 10.68/3.99  
% 10.68/3.99  %Foreground sorts:
% 10.68/3.99  
% 10.68/3.99  
% 10.68/3.99  %Background operators:
% 10.68/3.99  
% 10.68/3.99  
% 10.68/3.99  %Foreground operators:
% 10.68/3.99  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 10.68/3.99  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 10.68/3.99  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 10.68/3.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.68/3.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.68/3.99  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.68/3.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.68/3.99  tff('#skF_2', type, '#skF_2': $i).
% 10.68/3.99  tff('#skF_3', type, '#skF_3': $i).
% 10.68/3.99  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 10.68/3.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.68/3.99  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 10.68/3.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.68/3.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.68/3.99  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 10.68/3.99  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.68/3.99  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.68/3.99  tff(v1_compts_1, type, v1_compts_1: $i > $o).
% 10.68/3.99  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 10.68/3.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.68/3.99  
% 10.68/4.01  tff(f_120, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (((B = k1_xboole_0) => (v2_compts_1(B, A) <=> v1_compts_1(k1_pre_topc(A, B)))) & (v2_pre_topc(A) => ((B = k1_xboole_0) | (v2_compts_1(B, A) <=> v1_compts_1(k1_pre_topc(A, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_compts_1)).
% 10.68/4.01  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 10.68/4.01  tff(f_39, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 10.68/4.01  tff(f_47, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 10.68/4.01  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.68/4.01  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_pre_topc)).
% 10.68/4.01  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 10.68/4.01  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (v1_compts_1(A) <=> v2_compts_1(k2_struct_0(A), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_compts_1)).
% 10.68/4.01  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 10.68/4.01  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, k2_struct_0(B)) => (v2_compts_1(C, A) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((D = C) => v2_compts_1(D, B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_compts_1)).
% 10.68/4.01  tff(c_80, plain, (v2_compts_1('#skF_3', '#skF_2') | v1_compts_1(k1_pre_topc('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.68/4.01  tff(c_120, plain, (v1_compts_1(k1_pre_topc('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_80])).
% 10.68/4.01  tff(c_44, plain, (~v1_compts_1(k1_pre_topc('#skF_2', '#skF_3')) | ~v2_compts_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.68/4.01  tff(c_133, plain, (~v2_compts_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_44])).
% 10.68/4.01  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.68/4.01  tff(c_18, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.68/4.01  tff(c_105, plain, (![A_48]: (u1_struct_0(A_48)=k2_struct_0(A_48) | ~l1_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.68/4.01  tff(c_110, plain, (![A_49]: (u1_struct_0(A_49)=k2_struct_0(A_49) | ~l1_pre_topc(A_49))), inference(resolution, [status(thm)], [c_18, c_105])).
% 10.68/4.01  tff(c_114, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_110])).
% 10.68/4.01  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.68/4.01  tff(c_115, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_38])).
% 10.68/4.01  tff(c_172, plain, (![A_63, B_64]: (m1_pre_topc(k1_pre_topc(A_63, B_64), A_63) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.68/4.01  tff(c_177, plain, (![B_64]: (m1_pre_topc(k1_pre_topc('#skF_2', B_64), '#skF_2') | ~m1_subset_1(B_64, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_114, c_172])).
% 10.68/4.01  tff(c_203, plain, (![B_68]: (m1_pre_topc(k1_pre_topc('#skF_2', B_68), '#skF_2') | ~m1_subset_1(B_68, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_177])).
% 10.68/4.01  tff(c_212, plain, (m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_115, c_203])).
% 10.68/4.01  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.68/4.01  tff(c_263, plain, (![A_71, B_72]: (u1_struct_0(k1_pre_topc(A_71, B_72))=B_72 | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.68/4.01  tff(c_273, plain, (![B_72]: (u1_struct_0(k1_pre_topc('#skF_2', B_72))=B_72 | ~m1_subset_1(B_72, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_114, c_263])).
% 10.68/4.01  tff(c_289, plain, (![B_73]: (u1_struct_0(k1_pre_topc('#skF_2', B_73))=B_73 | ~m1_subset_1(B_73, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_273])).
% 10.68/4.01  tff(c_298, plain, (u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_115, c_289])).
% 10.68/4.01  tff(c_20, plain, (![B_11, A_9]: (l1_pre_topc(B_11) | ~m1_pre_topc(B_11, A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.68/4.01  tff(c_215, plain, (l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_212, c_20])).
% 10.68/4.01  tff(c_218, plain, (l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_215])).
% 10.68/4.01  tff(c_109, plain, (![A_8]: (u1_struct_0(A_8)=k2_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(resolution, [status(thm)], [c_18, c_105])).
% 10.68/4.01  tff(c_222, plain, (u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))=k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_218, c_109])).
% 10.68/4.01  tff(c_299, plain, (k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_298, c_222])).
% 10.68/4.01  tff(c_28, plain, (![A_22]: (v2_compts_1(k2_struct_0(A_22), A_22) | ~v1_compts_1(A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.68/4.01  tff(c_332, plain, (v2_compts_1('#skF_3', k1_pre_topc('#skF_2', '#skF_3')) | ~v1_compts_1(k1_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_299, c_28])).
% 10.68/4.01  tff(c_339, plain, (v2_compts_1('#skF_3', k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_218, c_120, c_332])).
% 10.68/4.01  tff(c_123, plain, (![A_54, B_55]: (r1_tarski(A_54, B_55) | ~m1_subset_1(A_54, k1_zfmisc_1(B_55)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.68/4.01  tff(c_131, plain, (r1_tarski('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_115, c_123])).
% 10.68/4.01  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.68/4.01  tff(c_518, plain, (![A_85, B_86, C_87]: ('#skF_1'(A_85, B_86, C_87)=C_87 | v2_compts_1(C_87, A_85) | ~r1_tarski(C_87, k2_struct_0(B_86)) | ~m1_subset_1(C_87, k1_zfmisc_1(u1_struct_0(A_85))) | ~m1_pre_topc(B_86, A_85) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.68/4.01  tff(c_1784, plain, (![A_135, B_136]: ('#skF_1'(A_135, B_136, k2_struct_0(B_136))=k2_struct_0(B_136) | v2_compts_1(k2_struct_0(B_136), A_135) | ~m1_subset_1(k2_struct_0(B_136), k1_zfmisc_1(u1_struct_0(A_135))) | ~m1_pre_topc(B_136, A_135) | ~l1_pre_topc(A_135))), inference(resolution, [status(thm)], [c_6, c_518])).
% 10.68/4.01  tff(c_4761, plain, (![A_214, B_215]: ('#skF_1'(A_214, B_215, k2_struct_0(B_215))=k2_struct_0(B_215) | v2_compts_1(k2_struct_0(B_215), A_214) | ~m1_pre_topc(B_215, A_214) | ~l1_pre_topc(A_214) | ~r1_tarski(k2_struct_0(B_215), u1_struct_0(A_214)))), inference(resolution, [status(thm)], [c_10, c_1784])).
% 10.68/4.01  tff(c_4822, plain, (![B_215]: ('#skF_1'('#skF_2', B_215, k2_struct_0(B_215))=k2_struct_0(B_215) | v2_compts_1(k2_struct_0(B_215), '#skF_2') | ~m1_pre_topc(B_215, '#skF_2') | ~l1_pre_topc('#skF_2') | ~r1_tarski(k2_struct_0(B_215), k2_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_114, c_4761])).
% 10.68/4.01  tff(c_5606, plain, (![B_226]: ('#skF_1'('#skF_2', B_226, k2_struct_0(B_226))=k2_struct_0(B_226) | v2_compts_1(k2_struct_0(B_226), '#skF_2') | ~m1_pre_topc(B_226, '#skF_2') | ~r1_tarski(k2_struct_0(B_226), k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_4822])).
% 10.68/4.01  tff(c_5630, plain, ('#skF_1'('#skF_2', k1_pre_topc('#skF_2', '#skF_3'), k2_struct_0(k1_pre_topc('#skF_2', '#skF_3')))=k2_struct_0(k1_pre_topc('#skF_2', '#skF_3')) | v2_compts_1(k2_struct_0(k1_pre_topc('#skF_2', '#skF_3')), '#skF_2') | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~r1_tarski('#skF_3', k2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_299, c_5606])).
% 10.68/4.01  tff(c_5651, plain, ('#skF_1'('#skF_2', k1_pre_topc('#skF_2', '#skF_3'), '#skF_3')='#skF_3' | v2_compts_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_212, c_299, c_299, c_299, c_5630])).
% 10.68/4.01  tff(c_5652, plain, ('#skF_1'('#skF_2', k1_pre_topc('#skF_2', '#skF_3'), '#skF_3')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_133, c_5651])).
% 10.68/4.01  tff(c_32, plain, (![A_23, B_35, C_41]: (~v2_compts_1('#skF_1'(A_23, B_35, C_41), B_35) | v2_compts_1(C_41, A_23) | ~r1_tarski(C_41, k2_struct_0(B_35)) | ~m1_subset_1(C_41, k1_zfmisc_1(u1_struct_0(A_23))) | ~m1_pre_topc(B_35, A_23) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.68/4.01  tff(c_5667, plain, (~v2_compts_1('#skF_3', k1_pre_topc('#skF_2', '#skF_3')) | v2_compts_1('#skF_3', '#skF_2') | ~r1_tarski('#skF_3', k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5652, c_32])).
% 10.68/4.01  tff(c_5683, plain, (v2_compts_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_212, c_115, c_114, c_6, c_299, c_339, c_5667])).
% 10.68/4.01  tff(c_5685, plain, $false, inference(negUnitSimplification, [status(thm)], [c_133, c_5683])).
% 10.68/4.01  tff(c_5687, plain, (~v1_compts_1(k1_pre_topc('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_80])).
% 10.68/4.01  tff(c_5729, plain, (![A_239, B_240]: (m1_pre_topc(k1_pre_topc(A_239, B_240), A_239) | ~m1_subset_1(B_240, k1_zfmisc_1(u1_struct_0(A_239))) | ~l1_pre_topc(A_239))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.68/4.01  tff(c_5734, plain, (![B_240]: (m1_pre_topc(k1_pre_topc('#skF_2', B_240), '#skF_2') | ~m1_subset_1(B_240, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_114, c_5729])).
% 10.68/4.01  tff(c_5759, plain, (![B_243]: (m1_pre_topc(k1_pre_topc('#skF_2', B_243), '#skF_2') | ~m1_subset_1(B_243, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_5734])).
% 10.68/4.01  tff(c_5768, plain, (m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_115, c_5759])).
% 10.68/4.01  tff(c_5771, plain, (l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_5768, c_20])).
% 10.68/4.01  tff(c_5774, plain, (l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_5771])).
% 10.68/4.01  tff(c_5803, plain, (![A_245, B_246]: (u1_struct_0(k1_pre_topc(A_245, B_246))=B_246 | ~m1_subset_1(B_246, k1_zfmisc_1(u1_struct_0(A_245))) | ~l1_pre_topc(A_245))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.68/4.01  tff(c_5813, plain, (![B_246]: (u1_struct_0(k1_pre_topc('#skF_2', B_246))=B_246 | ~m1_subset_1(B_246, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_114, c_5803])).
% 10.68/4.01  tff(c_5845, plain, (![B_249]: (u1_struct_0(k1_pre_topc('#skF_2', B_249))=B_249 | ~m1_subset_1(B_249, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_5813])).
% 10.68/4.01  tff(c_5854, plain, (u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_115, c_5845])).
% 10.68/4.01  tff(c_5778, plain, (u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))=k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_5774, c_109])).
% 10.68/4.01  tff(c_5855, plain, (k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5854, c_5778])).
% 10.68/4.01  tff(c_26, plain, (![A_22]: (v1_compts_1(A_22) | ~v2_compts_1(k2_struct_0(A_22), A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.68/4.01  tff(c_5882, plain, (v1_compts_1(k1_pre_topc('#skF_2', '#skF_3')) | ~v2_compts_1('#skF_3', k1_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_5855, c_26])).
% 10.68/4.01  tff(c_5889, plain, (v1_compts_1(k1_pre_topc('#skF_2', '#skF_3')) | ~v2_compts_1('#skF_3', k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5774, c_5882])).
% 10.68/4.01  tff(c_5890, plain, (~v2_compts_1('#skF_3', k1_pre_topc('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_5687, c_5889])).
% 10.68/4.01  tff(c_5686, plain, (v2_compts_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_80])).
% 10.68/4.01  tff(c_6867, plain, (![D_293, B_294, A_295]: (v2_compts_1(D_293, B_294) | ~m1_subset_1(D_293, k1_zfmisc_1(u1_struct_0(B_294))) | ~v2_compts_1(D_293, A_295) | ~r1_tarski(D_293, k2_struct_0(B_294)) | ~m1_subset_1(D_293, k1_zfmisc_1(u1_struct_0(A_295))) | ~m1_pre_topc(B_294, A_295) | ~l1_pre_topc(A_295))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.68/4.01  tff(c_7981, plain, (![A_336, B_337, A_338]: (v2_compts_1(A_336, B_337) | ~v2_compts_1(A_336, A_338) | ~r1_tarski(A_336, k2_struct_0(B_337)) | ~m1_subset_1(A_336, k1_zfmisc_1(u1_struct_0(A_338))) | ~m1_pre_topc(B_337, A_338) | ~l1_pre_topc(A_338) | ~r1_tarski(A_336, u1_struct_0(B_337)))), inference(resolution, [status(thm)], [c_10, c_6867])).
% 10.68/4.01  tff(c_8016, plain, (![A_336, B_337]: (v2_compts_1(A_336, B_337) | ~v2_compts_1(A_336, '#skF_2') | ~r1_tarski(A_336, k2_struct_0(B_337)) | ~m1_subset_1(A_336, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc(B_337, '#skF_2') | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_336, u1_struct_0(B_337)))), inference(superposition, [status(thm), theory('equality')], [c_114, c_7981])).
% 10.68/4.01  tff(c_17443, plain, (![A_502, B_503]: (v2_compts_1(A_502, B_503) | ~v2_compts_1(A_502, '#skF_2') | ~r1_tarski(A_502, k2_struct_0(B_503)) | ~m1_subset_1(A_502, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc(B_503, '#skF_2') | ~r1_tarski(A_502, u1_struct_0(B_503)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_8016])).
% 10.68/4.01  tff(c_17461, plain, (![B_503]: (v2_compts_1('#skF_3', B_503) | ~v2_compts_1('#skF_3', '#skF_2') | ~r1_tarski('#skF_3', k2_struct_0(B_503)) | ~m1_pre_topc(B_503, '#skF_2') | ~r1_tarski('#skF_3', u1_struct_0(B_503)))), inference(resolution, [status(thm)], [c_115, c_17443])).
% 10.68/4.01  tff(c_17474, plain, (![B_504]: (v2_compts_1('#skF_3', B_504) | ~r1_tarski('#skF_3', k2_struct_0(B_504)) | ~m1_pre_topc(B_504, '#skF_2') | ~r1_tarski('#skF_3', u1_struct_0(B_504)))), inference(demodulation, [status(thm), theory('equality')], [c_5686, c_17461])).
% 10.68/4.01  tff(c_17558, plain, (v2_compts_1('#skF_3', k1_pre_topc('#skF_2', '#skF_3')) | ~r1_tarski('#skF_3', k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))) | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~r1_tarski('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5854, c_17474])).
% 10.68/4.01  tff(c_17593, plain, (v2_compts_1('#skF_3', k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_5768, c_6, c_5855, c_17558])).
% 10.68/4.01  tff(c_17595, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5890, c_17593])).
% 10.68/4.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.68/4.01  
% 10.68/4.01  Inference rules
% 10.68/4.01  ----------------------
% 10.68/4.01  #Ref     : 0
% 10.68/4.01  #Sup     : 4482
% 10.68/4.01  #Fact    : 0
% 10.68/4.01  #Define  : 0
% 10.68/4.01  #Split   : 14
% 10.68/4.01  #Chain   : 0
% 10.68/4.01  #Close   : 0
% 10.68/4.01  
% 10.68/4.01  Ordering : KBO
% 10.68/4.01  
% 10.68/4.01  Simplification rules
% 10.68/4.01  ----------------------
% 10.68/4.01  #Subsume      : 657
% 10.68/4.01  #Demod        : 3850
% 10.68/4.01  #Tautology    : 827
% 10.68/4.01  #SimpNegUnit  : 40
% 10.68/4.01  #BackRed      : 7
% 10.68/4.01  
% 10.68/4.01  #Partial instantiations: 0
% 10.68/4.01  #Strategies tried      : 1
% 10.68/4.01  
% 10.68/4.01  Timing (in seconds)
% 10.68/4.01  ----------------------
% 10.68/4.01  Preprocessing        : 0.36
% 10.68/4.01  Parsing              : 0.19
% 10.68/4.01  CNF conversion       : 0.03
% 10.68/4.01  Main loop            : 2.97
% 10.68/4.01  Inferencing          : 0.68
% 10.68/4.01  Reduction            : 1.01
% 10.68/4.01  Demodulation         : 0.71
% 10.68/4.01  BG Simplification    : 0.10
% 10.68/4.01  Subsumption          : 0.99
% 10.68/4.01  Abstraction          : 0.11
% 10.68/4.01  MUC search           : 0.00
% 10.68/4.01  Cooper               : 0.00
% 10.68/4.01  Total                : 3.37
% 10.68/4.01  Index Insertion      : 0.00
% 10.68/4.01  Index Deletion       : 0.00
% 10.68/4.01  Index Matching       : 0.00
% 10.68/4.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
