%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:04 EST 2020

% Result     : Theorem 38.65s
% Output     : CNFRefutation 38.65s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 775 expanded)
%              Number of leaves         :   37 ( 268 expanded)
%              Depth                    :   14
%              Number of atoms          :  408 (2659 expanded)
%              Number of equality atoms :   26 (  63 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(v1_yellow_0,type,(
    v1_yellow_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_117,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_146,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v1_yellow_0(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v2_waybel_0(B,A)
              & v13_waybel_0(B,A)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ( v1_subset_1(B,u1_struct_0(A))
            <=> ~ r2_hidden(k3_yellow_0(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(k3_yellow_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).

tff(f_91,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,k3_yellow_0(A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_yellow_0)).

tff(f_110,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v13_waybel_0(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( ( r2_hidden(C,B)
                        & r1_orders_2(A,C,D) )
                     => r2_hidden(D,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                <=> r2_hidden(D,C) ) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_194,plain,(
    ! [A_84,B_85] :
      ( ~ r2_hidden('#skF_1'(A_84,B_85),B_85)
      | r1_tarski(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_203,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_194])).

tff(c_26,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(A_21,k1_zfmisc_1(B_22))
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_89,plain,(
    ! [B_65] :
      ( ~ v1_subset_1(B_65,B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_94,plain,(
    ! [B_22] :
      ( ~ v1_subset_1(B_22,B_22)
      | ~ r1_tarski(B_22,B_22) ) ),
    inference(resolution,[status(thm)],[c_26,c_89])).

tff(c_216,plain,(
    ! [B_22] : ~ v1_subset_1(B_22,B_22) ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_94])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_80,plain,(
    ! [A_63,B_64] :
      ( r1_tarski(A_63,B_64)
      | ~ m1_subset_1(A_63,k1_zfmisc_1(B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_88,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_50,c_80])).

tff(c_309,plain,(
    ! [A_106,C_107,B_108] :
      ( m1_subset_1(A_106,C_107)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(C_107))
      | ~ r2_hidden(A_106,B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_329,plain,(
    ! [A_110,B_111,A_112] :
      ( m1_subset_1(A_110,B_111)
      | ~ r2_hidden(A_110,A_112)
      | ~ r1_tarski(A_112,B_111) ) ),
    inference(resolution,[status(thm)],[c_26,c_309])).

tff(c_572,plain,(
    ! [A_148,B_149,B_150] :
      ( m1_subset_1('#skF_1'(A_148,B_149),B_150)
      | ~ r1_tarski(A_148,B_150)
      | r1_tarski(A_148,B_149) ) ),
    inference(resolution,[status(thm)],[c_6,c_329])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( r2_hidden(A_19,B_20)
      | v1_xboole_0(B_20)
      | ~ m1_subset_1(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_205,plain,(
    ! [C_86,B_87,A_88] :
      ( r2_hidden(C_86,B_87)
      | ~ r2_hidden(C_86,A_88)
      | ~ r1_tarski(A_88,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_495,plain,(
    ! [A_133,B_134,B_135] :
      ( r2_hidden(A_133,B_134)
      | ~ r1_tarski(B_135,B_134)
      | v1_xboole_0(B_135)
      | ~ m1_subset_1(A_133,B_135) ) ),
    inference(resolution,[status(thm)],[c_22,c_205])).

tff(c_503,plain,(
    ! [A_133] :
      ( r2_hidden(A_133,u1_struct_0('#skF_5'))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_133,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_88,c_495])).

tff(c_510,plain,(
    ! [A_136] :
      ( r2_hidden(A_136,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_136,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_503])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_531,plain,(
    ! [A_1] :
      ( r1_tarski(A_1,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_1'(A_1,u1_struct_0('#skF_5')),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_510,c_4])).

tff(c_595,plain,(
    ! [A_148] :
      ( ~ r1_tarski(A_148,'#skF_6')
      | r1_tarski(A_148,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_572,c_531])).

tff(c_462,plain,(
    ! [A_128,B_129,B_130] :
      ( r2_hidden('#skF_1'(A_128,B_129),B_130)
      | ~ r1_tarski(A_128,B_130)
      | r1_tarski(A_128,B_129) ) ),
    inference(resolution,[status(thm)],[c_6,c_205])).

tff(c_326,plain,(
    ! [A_106,B_22,A_21] :
      ( m1_subset_1(A_106,B_22)
      | ~ r2_hidden(A_106,A_21)
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(resolution,[status(thm)],[c_26,c_309])).

tff(c_1524,plain,(
    ! [A_227,B_228,B_229,B_230] :
      ( m1_subset_1('#skF_1'(A_227,B_228),B_229)
      | ~ r1_tarski(B_230,B_229)
      | ~ r1_tarski(A_227,B_230)
      | r1_tarski(A_227,B_228) ) ),
    inference(resolution,[status(thm)],[c_462,c_326])).

tff(c_2637,plain,(
    ! [A_313,B_314,A_315] :
      ( m1_subset_1('#skF_1'(A_313,B_314),u1_struct_0('#skF_5'))
      | ~ r1_tarski(A_313,A_315)
      | r1_tarski(A_313,B_314)
      | ~ r1_tarski(A_315,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_595,c_1524])).

tff(c_2667,plain,(
    ! [B_314] :
      ( m1_subset_1('#skF_1'('#skF_6',B_314),u1_struct_0('#skF_5'))
      | r1_tarski('#skF_6',B_314)
      | ~ r1_tarski(u1_struct_0('#skF_5'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_88,c_2637])).

tff(c_2668,plain,(
    ~ r1_tarski(u1_struct_0('#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_2667])).

tff(c_189,plain,(
    ! [A_82,B_83] :
      ( r2_hidden('#skF_1'(A_82,B_83),A_82)
      | r1_tarski(A_82,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_20,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,B_18)
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_193,plain,(
    ! [A_82,B_83] :
      ( m1_subset_1('#skF_1'(A_82,B_83),A_82)
      | r1_tarski(A_82,B_83) ) ),
    inference(resolution,[status(thm)],[c_189,c_20])).

tff(c_52,plain,(
    v13_waybel_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_76,plain,
    ( v1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_101,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_105,plain,
    ( v1_xboole_0('#skF_6')
    | ~ m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_22,c_101])).

tff(c_108,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_105])).

tff(c_58,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_70,plain,
    ( r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
    | ~ v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_102,plain,(
    ~ v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_142,plain,(
    ! [B_80,A_81] :
      ( v1_subset_1(B_80,A_81)
      | B_80 = A_81
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_152,plain,
    ( v1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_50,c_142])).

tff(c_157,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_152])).

tff(c_30,plain,(
    ! [A_26] :
      ( m1_subset_1(k3_yellow_0(A_26),u1_struct_0(A_26))
      | ~ l1_orders_2(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_165,plain,
    ( m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6')
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_30])).

tff(c_169,plain,(
    m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_165])).

tff(c_171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_169])).

tff(c_172,plain,(
    r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_172])).

tff(c_182,plain,(
    r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_62,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_60,plain,(
    v1_yellow_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_327,plain,(
    ! [A_106] :
      ( m1_subset_1(A_106,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_106,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_50,c_309])).

tff(c_32,plain,(
    ! [A_27,B_29] :
      ( r1_orders_2(A_27,k3_yellow_0(A_27),B_29)
      | ~ m1_subset_1(B_29,u1_struct_0(A_27))
      | ~ l1_orders_2(A_27)
      | ~ v1_yellow_0(A_27)
      | ~ v5_orders_2(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1695,plain,(
    ! [D_240,B_241,A_242,C_243] :
      ( r2_hidden(D_240,B_241)
      | ~ r1_orders_2(A_242,C_243,D_240)
      | ~ r2_hidden(C_243,B_241)
      | ~ m1_subset_1(D_240,u1_struct_0(A_242))
      | ~ m1_subset_1(C_243,u1_struct_0(A_242))
      | ~ v13_waybel_0(B_241,A_242)
      | ~ m1_subset_1(B_241,k1_zfmisc_1(u1_struct_0(A_242)))
      | ~ l1_orders_2(A_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_4460,plain,(
    ! [B_430,B_431,A_432] :
      ( r2_hidden(B_430,B_431)
      | ~ r2_hidden(k3_yellow_0(A_432),B_431)
      | ~ m1_subset_1(k3_yellow_0(A_432),u1_struct_0(A_432))
      | ~ v13_waybel_0(B_431,A_432)
      | ~ m1_subset_1(B_431,k1_zfmisc_1(u1_struct_0(A_432)))
      | ~ m1_subset_1(B_430,u1_struct_0(A_432))
      | ~ l1_orders_2(A_432)
      | ~ v1_yellow_0(A_432)
      | ~ v5_orders_2(A_432)
      | v2_struct_0(A_432) ) ),
    inference(resolution,[status(thm)],[c_32,c_1695])).

tff(c_4471,plain,(
    ! [B_430,B_431] :
      ( r2_hidden(B_430,B_431)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_431)
      | ~ v13_waybel_0(B_431,'#skF_5')
      | ~ m1_subset_1(B_431,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_430,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v1_yellow_0('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_327,c_4460])).

tff(c_4494,plain,(
    ! [B_430,B_431] :
      ( r2_hidden(B_430,B_431)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_431)
      | ~ v13_waybel_0(B_431,'#skF_5')
      | ~ m1_subset_1(B_431,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_430,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_62,c_60,c_58,c_4471])).

tff(c_4615,plain,(
    ! [B_442,B_443] :
      ( r2_hidden(B_442,B_443)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_443)
      | ~ v13_waybel_0(B_443,'#skF_5')
      | ~ m1_subset_1(B_443,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_442,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_4494])).

tff(c_4665,plain,(
    ! [B_442] :
      ( r2_hidden(B_442,'#skF_6')
      | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
      | ~ v13_waybel_0('#skF_6','#skF_5')
      | ~ m1_subset_1(B_442,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_50,c_4615])).

tff(c_4685,plain,(
    ! [B_444] :
      ( r2_hidden(B_444,'#skF_6')
      | ~ m1_subset_1(B_444,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_182,c_4665])).

tff(c_4988,plain,(
    ! [B_454] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_454),'#skF_6')
      | r1_tarski(u1_struct_0('#skF_5'),B_454) ) ),
    inference(resolution,[status(thm)],[c_193,c_4685])).

tff(c_4998,plain,(
    r1_tarski(u1_struct_0('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_4988,c_4])).

tff(c_5008,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2668,c_2668,c_4998])).

tff(c_5010,plain,(
    r1_tarski(u1_struct_0('#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_2667])).

tff(c_1309,plain,(
    ! [A_209,B_210,C_211] :
      ( r2_hidden('#skF_2'(A_209,B_210,C_211),B_210)
      | r2_hidden('#skF_2'(A_209,B_210,C_211),C_211)
      | C_211 = B_210
      | ~ m1_subset_1(C_211,k1_zfmisc_1(A_209))
      | ~ m1_subset_1(B_210,k1_zfmisc_1(A_209)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1360,plain,(
    ! [A_209,B_210,C_211,B_2] :
      ( r2_hidden('#skF_2'(A_209,B_210,C_211),B_2)
      | ~ r1_tarski(C_211,B_2)
      | r2_hidden('#skF_2'(A_209,B_210,C_211),B_210)
      | C_211 = B_210
      | ~ m1_subset_1(C_211,k1_zfmisc_1(A_209))
      | ~ m1_subset_1(B_210,k1_zfmisc_1(A_209)) ) ),
    inference(resolution,[status(thm)],[c_1309,c_2])).

tff(c_5894,plain,(
    ! [C_211,B_2,A_209] :
      ( ~ r1_tarski(C_211,B_2)
      | C_211 = B_2
      | ~ m1_subset_1(C_211,k1_zfmisc_1(A_209))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_209))
      | r2_hidden('#skF_2'(A_209,B_2,C_211),B_2) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_1360])).

tff(c_1353,plain,(
    ! [A_209,B_210,C_211,B_2] :
      ( r2_hidden('#skF_2'(A_209,B_210,C_211),B_2)
      | ~ r1_tarski(B_210,B_2)
      | r2_hidden('#skF_2'(A_209,B_210,C_211),C_211)
      | C_211 = B_210
      | ~ m1_subset_1(C_211,k1_zfmisc_1(A_209))
      | ~ m1_subset_1(B_210,k1_zfmisc_1(A_209)) ) ),
    inference(resolution,[status(thm)],[c_1309,c_2])).

tff(c_10598,plain,(
    ! [B_670,C_671,A_672] :
      ( ~ r1_tarski(B_670,C_671)
      | C_671 = B_670
      | ~ m1_subset_1(C_671,k1_zfmisc_1(A_672))
      | ~ m1_subset_1(B_670,k1_zfmisc_1(A_672))
      | r2_hidden('#skF_2'(A_672,B_670,C_671),C_671) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_1353])).

tff(c_12,plain,(
    ! [A_10,B_11,C_15] :
      ( ~ r2_hidden('#skF_2'(A_10,B_11,C_15),C_15)
      | ~ r2_hidden('#skF_2'(A_10,B_11,C_15),B_11)
      | C_15 = B_11
      | ~ m1_subset_1(C_15,k1_zfmisc_1(A_10))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_52180,plain,(
    ! [A_1520,B_1521,C_1522] :
      ( ~ r2_hidden('#skF_2'(A_1520,B_1521,C_1522),B_1521)
      | ~ r1_tarski(B_1521,C_1522)
      | C_1522 = B_1521
      | ~ m1_subset_1(C_1522,k1_zfmisc_1(A_1520))
      | ~ m1_subset_1(B_1521,k1_zfmisc_1(A_1520)) ) ),
    inference(resolution,[status(thm)],[c_10598,c_12])).

tff(c_52464,plain,(
    ! [B_1523,C_1524,A_1525] :
      ( ~ r1_tarski(B_1523,C_1524)
      | ~ r1_tarski(C_1524,B_1523)
      | C_1524 = B_1523
      | ~ m1_subset_1(C_1524,k1_zfmisc_1(A_1525))
      | ~ m1_subset_1(B_1523,k1_zfmisc_1(A_1525)) ) ),
    inference(resolution,[status(thm)],[c_5894,c_52180])).

tff(c_52554,plain,(
    ! [A_1525] :
      ( ~ r1_tarski(u1_struct_0('#skF_5'),'#skF_6')
      | u1_struct_0('#skF_5') = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_1525))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1525)) ) ),
    inference(resolution,[status(thm)],[c_88,c_52464])).

tff(c_52606,plain,(
    ! [A_1525] :
      ( u1_struct_0('#skF_5') = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_1525))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1525)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5010,c_52554])).

tff(c_52608,plain,(
    ! [A_1526] :
      ( ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_1526))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1526)) ) ),
    inference(splitLeft,[status(thm)],[c_52606])).

tff(c_52614,plain,(
    ! [B_1527] :
      ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(B_1527))
      | ~ r1_tarski(u1_struct_0('#skF_5'),B_1527) ) ),
    inference(resolution,[status(thm)],[c_26,c_52608])).

tff(c_52631,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ r1_tarski(u1_struct_0('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_595,c_52614])).

tff(c_52645,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5010,c_50,c_52631])).

tff(c_52646,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_52606])).

tff(c_350,plain,(
    ! [A_115,B_116] :
      ( r1_tarski(A_115,B_116)
      | v1_xboole_0(B_116)
      | ~ m1_subset_1('#skF_1'(A_115,B_116),B_116) ) ),
    inference(resolution,[status(thm)],[c_22,c_194])).

tff(c_363,plain,(
    ! [A_115] :
      ( r1_tarski(A_115,u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_1'(A_115,u1_struct_0('#skF_5')),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_327,c_350])).

tff(c_379,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_363])).

tff(c_53078,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52646,c_379])).

tff(c_53092,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_53078])).

tff(c_53094,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_363])).

tff(c_53252,plain,(
    ! [A_1553,B_1554,B_1555] :
      ( r2_hidden('#skF_1'(A_1553,B_1554),B_1555)
      | ~ r1_tarski(A_1553,B_1555)
      | r1_tarski(A_1553,B_1554) ) ),
    inference(resolution,[status(thm)],[c_6,c_205])).

tff(c_53093,plain,(
    ! [A_115] :
      ( r1_tarski(A_115,u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_1'(A_115,u1_struct_0('#skF_5')),'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_363])).

tff(c_53276,plain,(
    ! [A_1556] :
      ( ~ r1_tarski(A_1556,'#skF_6')
      | r1_tarski(A_1556,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_53252,c_53093])).

tff(c_214,plain,(
    ! [A_19,B_87,B_20] :
      ( r2_hidden(A_19,B_87)
      | ~ r1_tarski(B_20,B_87)
      | v1_xboole_0(B_20)
      | ~ m1_subset_1(A_19,B_20) ) ),
    inference(resolution,[status(thm)],[c_22,c_205])).

tff(c_53797,plain,(
    ! [A_1606,A_1607] :
      ( r2_hidden(A_1606,u1_struct_0('#skF_5'))
      | v1_xboole_0(A_1607)
      | ~ m1_subset_1(A_1606,A_1607)
      | ~ r1_tarski(A_1607,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_53276,c_214])).

tff(c_53813,plain,(
    ! [A_106] :
      ( r2_hidden(A_106,u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ r1_tarski(u1_struct_0('#skF_5'),'#skF_6')
      | ~ r2_hidden(A_106,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_327,c_53797])).

tff(c_53840,plain,(
    ! [A_106] :
      ( r2_hidden(A_106,u1_struct_0('#skF_5'))
      | ~ r1_tarski(u1_struct_0('#skF_5'),'#skF_6')
      | ~ r2_hidden(A_106,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_53094,c_53813])).

tff(c_53853,plain,(
    ~ r1_tarski(u1_struct_0('#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_53840])).

tff(c_54444,plain,(
    ! [D_1653,B_1654,A_1655,C_1656] :
      ( r2_hidden(D_1653,B_1654)
      | ~ r1_orders_2(A_1655,C_1656,D_1653)
      | ~ r2_hidden(C_1656,B_1654)
      | ~ m1_subset_1(D_1653,u1_struct_0(A_1655))
      | ~ m1_subset_1(C_1656,u1_struct_0(A_1655))
      | ~ v13_waybel_0(B_1654,A_1655)
      | ~ m1_subset_1(B_1654,k1_zfmisc_1(u1_struct_0(A_1655)))
      | ~ l1_orders_2(A_1655) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_57184,plain,(
    ! [B_1852,B_1853,A_1854] :
      ( r2_hidden(B_1852,B_1853)
      | ~ r2_hidden(k3_yellow_0(A_1854),B_1853)
      | ~ m1_subset_1(k3_yellow_0(A_1854),u1_struct_0(A_1854))
      | ~ v13_waybel_0(B_1853,A_1854)
      | ~ m1_subset_1(B_1853,k1_zfmisc_1(u1_struct_0(A_1854)))
      | ~ m1_subset_1(B_1852,u1_struct_0(A_1854))
      | ~ l1_orders_2(A_1854)
      | ~ v1_yellow_0(A_1854)
      | ~ v5_orders_2(A_1854)
      | v2_struct_0(A_1854) ) ),
    inference(resolution,[status(thm)],[c_32,c_54444])).

tff(c_57195,plain,(
    ! [B_1852,B_1853] :
      ( r2_hidden(B_1852,B_1853)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1853)
      | ~ v13_waybel_0(B_1853,'#skF_5')
      | ~ m1_subset_1(B_1853,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1852,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v1_yellow_0('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_327,c_57184])).

tff(c_57218,plain,(
    ! [B_1852,B_1853] :
      ( r2_hidden(B_1852,B_1853)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1853)
      | ~ v13_waybel_0(B_1853,'#skF_5')
      | ~ m1_subset_1(B_1853,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1852,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_62,c_60,c_58,c_57195])).

tff(c_57343,plain,(
    ! [B_1864,B_1865] :
      ( r2_hidden(B_1864,B_1865)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_1865)
      | ~ v13_waybel_0(B_1865,'#skF_5')
      | ~ m1_subset_1(B_1865,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1864,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_57218])).

tff(c_57393,plain,(
    ! [B_1864] :
      ( r2_hidden(B_1864,'#skF_6')
      | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
      | ~ v13_waybel_0('#skF_6','#skF_5')
      | ~ m1_subset_1(B_1864,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_50,c_57343])).

tff(c_57413,plain,(
    ! [B_1866] :
      ( r2_hidden(B_1866,'#skF_6')
      | ~ m1_subset_1(B_1866,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_182,c_57393])).

tff(c_57736,plain,(
    ! [B_1876] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_1876),'#skF_6')
      | r1_tarski(u1_struct_0('#skF_5'),B_1876) ) ),
    inference(resolution,[status(thm)],[c_193,c_57413])).

tff(c_57750,plain,(
    r1_tarski(u1_struct_0('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_57736,c_4])).

tff(c_57762,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53853,c_53853,c_57750])).

tff(c_57764,plain,(
    r1_tarski(u1_struct_0('#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_53840])).

tff(c_53270,plain,(
    ! [A_1553] :
      ( ~ r1_tarski(A_1553,'#skF_6')
      | r1_tarski(A_1553,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_53252,c_53093])).

tff(c_58302,plain,(
    ! [A_1905,B_1906,C_1907] :
      ( r2_hidden('#skF_2'(A_1905,B_1906,C_1907),B_1906)
      | r2_hidden('#skF_2'(A_1905,B_1906,C_1907),C_1907)
      | C_1907 = B_1906
      | ~ m1_subset_1(C_1907,k1_zfmisc_1(A_1905))
      | ~ m1_subset_1(B_1906,k1_zfmisc_1(A_1905)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_58343,plain,(
    ! [A_1905,B_1906,C_1907,B_2] :
      ( r2_hidden('#skF_2'(A_1905,B_1906,C_1907),B_2)
      | ~ r1_tarski(C_1907,B_2)
      | r2_hidden('#skF_2'(A_1905,B_1906,C_1907),B_1906)
      | C_1907 = B_1906
      | ~ m1_subset_1(C_1907,k1_zfmisc_1(A_1905))
      | ~ m1_subset_1(B_1906,k1_zfmisc_1(A_1905)) ) ),
    inference(resolution,[status(thm)],[c_58302,c_2])).

tff(c_61097,plain,(
    ! [C_1907,B_1906,A_1905] :
      ( ~ r1_tarski(C_1907,B_1906)
      | C_1907 = B_1906
      | ~ m1_subset_1(C_1907,k1_zfmisc_1(A_1905))
      | ~ m1_subset_1(B_1906,k1_zfmisc_1(A_1905))
      | r2_hidden('#skF_2'(A_1905,B_1906,C_1907),B_1906) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_58343])).

tff(c_58337,plain,(
    ! [A_1905,B_1906,C_1907,B_2] :
      ( r2_hidden('#skF_2'(A_1905,B_1906,C_1907),B_2)
      | ~ r1_tarski(B_1906,B_2)
      | r2_hidden('#skF_2'(A_1905,B_1906,C_1907),C_1907)
      | C_1907 = B_1906
      | ~ m1_subset_1(C_1907,k1_zfmisc_1(A_1905))
      | ~ m1_subset_1(B_1906,k1_zfmisc_1(A_1905)) ) ),
    inference(resolution,[status(thm)],[c_58302,c_2])).

tff(c_66835,plain,(
    ! [B_2237,C_2238,A_2239] :
      ( ~ r1_tarski(B_2237,C_2238)
      | C_2238 = B_2237
      | ~ m1_subset_1(C_2238,k1_zfmisc_1(A_2239))
      | ~ m1_subset_1(B_2237,k1_zfmisc_1(A_2239))
      | r2_hidden('#skF_2'(A_2239,B_2237,C_2238),C_2238) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_58337])).

tff(c_106692,plain,(
    ! [A_3075,B_3076,C_3077] :
      ( ~ r2_hidden('#skF_2'(A_3075,B_3076,C_3077),B_3076)
      | ~ r1_tarski(B_3076,C_3077)
      | C_3077 = B_3076
      | ~ m1_subset_1(C_3077,k1_zfmisc_1(A_3075))
      | ~ m1_subset_1(B_3076,k1_zfmisc_1(A_3075)) ) ),
    inference(resolution,[status(thm)],[c_66835,c_12])).

tff(c_106969,plain,(
    ! [B_3078,C_3079,A_3080] :
      ( ~ r1_tarski(B_3078,C_3079)
      | ~ r1_tarski(C_3079,B_3078)
      | C_3079 = B_3078
      | ~ m1_subset_1(C_3079,k1_zfmisc_1(A_3080))
      | ~ m1_subset_1(B_3078,k1_zfmisc_1(A_3080)) ) ),
    inference(resolution,[status(thm)],[c_61097,c_106692])).

tff(c_107061,plain,(
    ! [A_3080] :
      ( ~ r1_tarski(u1_struct_0('#skF_5'),'#skF_6')
      | u1_struct_0('#skF_5') = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_3080))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_3080)) ) ),
    inference(resolution,[status(thm)],[c_88,c_106969])).

tff(c_107114,plain,(
    ! [A_3080] :
      ( u1_struct_0('#skF_5') = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_3080))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_3080)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57764,c_107061])).

tff(c_107116,plain,(
    ! [A_3081] :
      ( ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_3081))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_3081)) ) ),
    inference(splitLeft,[status(thm)],[c_107114])).

tff(c_107122,plain,(
    ! [B_3082] :
      ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(B_3082))
      | ~ r1_tarski(u1_struct_0('#skF_5'),B_3082) ) ),
    inference(resolution,[status(thm)],[c_26,c_107116])).

tff(c_107139,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ r1_tarski(u1_struct_0('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_53270,c_107122])).

tff(c_107153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_57764,c_50,c_107139])).

tff(c_107154,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_107114])).

tff(c_181,plain,(
    v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_107594,plain,(
    v1_subset_1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107154,c_181])).

tff(c_107606,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_216,c_107594])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:41:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 38.65/29.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 38.65/29.07  
% 38.65/29.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 38.65/29.07  %$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 38.65/29.07  
% 38.65/29.07  %Foreground sorts:
% 38.65/29.07  
% 38.65/29.07  
% 38.65/29.07  %Background operators:
% 38.65/29.07  
% 38.65/29.07  
% 38.65/29.07  %Foreground operators:
% 38.65/29.07  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 38.65/29.07  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 38.65/29.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 38.65/29.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 38.65/29.07  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 38.65/29.07  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 38.65/29.07  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 38.65/29.07  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 38.65/29.07  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 38.65/29.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 38.65/29.07  tff('#skF_5', type, '#skF_5': $i).
% 38.65/29.07  tff('#skF_6', type, '#skF_6': $i).
% 38.65/29.07  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 38.65/29.07  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 38.65/29.07  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 38.65/29.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 38.65/29.07  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 38.65/29.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 38.65/29.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 38.65/29.07  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 38.65/29.07  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 38.65/29.07  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 38.65/29.07  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 38.65/29.07  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 38.65/29.07  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 38.65/29.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 38.65/29.07  
% 38.65/29.10  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 38.65/29.10  tff(f_67, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 38.65/29.10  tff(f_117, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 38.65/29.10  tff(f_146, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_subset_1(B, u1_struct_0(A)) <=> ~r2_hidden(k3_yellow_0(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_7)).
% 38.65/29.10  tff(f_73, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 38.65/29.10  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 38.65/29.10  tff(f_57, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 38.65/29.10  tff(f_77, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(k3_yellow_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow_0)).
% 38.65/29.10  tff(f_91, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, k3_yellow_0(A), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_yellow_0)).
% 38.65/29.10  tff(f_110, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v13_waybel_0(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r1_orders_2(A, C, D)) => r2_hidden(D, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_waybel_0)).
% 38.65/29.10  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_subset_1)).
% 38.65/29.10  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 38.65/29.10  tff(c_194, plain, (![A_84, B_85]: (~r2_hidden('#skF_1'(A_84, B_85), B_85) | r1_tarski(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_32])).
% 38.65/29.10  tff(c_203, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_194])).
% 38.65/29.10  tff(c_26, plain, (![A_21, B_22]: (m1_subset_1(A_21, k1_zfmisc_1(B_22)) | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_67])).
% 38.65/29.10  tff(c_89, plain, (![B_65]: (~v1_subset_1(B_65, B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(B_65)))), inference(cnfTransformation, [status(thm)], [f_117])).
% 38.65/29.10  tff(c_94, plain, (![B_22]: (~v1_subset_1(B_22, B_22) | ~r1_tarski(B_22, B_22))), inference(resolution, [status(thm)], [c_26, c_89])).
% 38.65/29.10  tff(c_216, plain, (![B_22]: (~v1_subset_1(B_22, B_22))), inference(demodulation, [status(thm), theory('equality')], [c_203, c_94])).
% 38.65/29.10  tff(c_56, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_146])).
% 38.65/29.10  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_146])).
% 38.65/29.10  tff(c_80, plain, (![A_63, B_64]: (r1_tarski(A_63, B_64) | ~m1_subset_1(A_63, k1_zfmisc_1(B_64)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 38.65/29.10  tff(c_88, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_80])).
% 38.65/29.10  tff(c_309, plain, (![A_106, C_107, B_108]: (m1_subset_1(A_106, C_107) | ~m1_subset_1(B_108, k1_zfmisc_1(C_107)) | ~r2_hidden(A_106, B_108))), inference(cnfTransformation, [status(thm)], [f_73])).
% 38.65/29.10  tff(c_329, plain, (![A_110, B_111, A_112]: (m1_subset_1(A_110, B_111) | ~r2_hidden(A_110, A_112) | ~r1_tarski(A_112, B_111))), inference(resolution, [status(thm)], [c_26, c_309])).
% 38.65/29.10  tff(c_572, plain, (![A_148, B_149, B_150]: (m1_subset_1('#skF_1'(A_148, B_149), B_150) | ~r1_tarski(A_148, B_150) | r1_tarski(A_148, B_149))), inference(resolution, [status(thm)], [c_6, c_329])).
% 38.65/29.10  tff(c_22, plain, (![A_19, B_20]: (r2_hidden(A_19, B_20) | v1_xboole_0(B_20) | ~m1_subset_1(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 38.65/29.10  tff(c_205, plain, (![C_86, B_87, A_88]: (r2_hidden(C_86, B_87) | ~r2_hidden(C_86, A_88) | ~r1_tarski(A_88, B_87))), inference(cnfTransformation, [status(thm)], [f_32])).
% 38.65/29.10  tff(c_495, plain, (![A_133, B_134, B_135]: (r2_hidden(A_133, B_134) | ~r1_tarski(B_135, B_134) | v1_xboole_0(B_135) | ~m1_subset_1(A_133, B_135))), inference(resolution, [status(thm)], [c_22, c_205])).
% 38.65/29.10  tff(c_503, plain, (![A_133]: (r2_hidden(A_133, u1_struct_0('#skF_5')) | v1_xboole_0('#skF_6') | ~m1_subset_1(A_133, '#skF_6'))), inference(resolution, [status(thm)], [c_88, c_495])).
% 38.65/29.10  tff(c_510, plain, (![A_136]: (r2_hidden(A_136, u1_struct_0('#skF_5')) | ~m1_subset_1(A_136, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_56, c_503])).
% 38.65/29.10  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 38.65/29.10  tff(c_531, plain, (![A_1]: (r1_tarski(A_1, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_1'(A_1, u1_struct_0('#skF_5')), '#skF_6'))), inference(resolution, [status(thm)], [c_510, c_4])).
% 38.65/29.10  tff(c_595, plain, (![A_148]: (~r1_tarski(A_148, '#skF_6') | r1_tarski(A_148, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_572, c_531])).
% 38.65/29.10  tff(c_462, plain, (![A_128, B_129, B_130]: (r2_hidden('#skF_1'(A_128, B_129), B_130) | ~r1_tarski(A_128, B_130) | r1_tarski(A_128, B_129))), inference(resolution, [status(thm)], [c_6, c_205])).
% 38.65/29.10  tff(c_326, plain, (![A_106, B_22, A_21]: (m1_subset_1(A_106, B_22) | ~r2_hidden(A_106, A_21) | ~r1_tarski(A_21, B_22))), inference(resolution, [status(thm)], [c_26, c_309])).
% 38.65/29.10  tff(c_1524, plain, (![A_227, B_228, B_229, B_230]: (m1_subset_1('#skF_1'(A_227, B_228), B_229) | ~r1_tarski(B_230, B_229) | ~r1_tarski(A_227, B_230) | r1_tarski(A_227, B_228))), inference(resolution, [status(thm)], [c_462, c_326])).
% 38.65/29.10  tff(c_2637, plain, (![A_313, B_314, A_315]: (m1_subset_1('#skF_1'(A_313, B_314), u1_struct_0('#skF_5')) | ~r1_tarski(A_313, A_315) | r1_tarski(A_313, B_314) | ~r1_tarski(A_315, '#skF_6'))), inference(resolution, [status(thm)], [c_595, c_1524])).
% 38.65/29.10  tff(c_2667, plain, (![B_314]: (m1_subset_1('#skF_1'('#skF_6', B_314), u1_struct_0('#skF_5')) | r1_tarski('#skF_6', B_314) | ~r1_tarski(u1_struct_0('#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_88, c_2637])).
% 38.65/29.10  tff(c_2668, plain, (~r1_tarski(u1_struct_0('#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_2667])).
% 38.65/29.10  tff(c_189, plain, (![A_82, B_83]: (r2_hidden('#skF_1'(A_82, B_83), A_82) | r1_tarski(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_32])).
% 38.65/29.10  tff(c_20, plain, (![A_17, B_18]: (m1_subset_1(A_17, B_18) | ~r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 38.65/29.10  tff(c_193, plain, (![A_82, B_83]: (m1_subset_1('#skF_1'(A_82, B_83), A_82) | r1_tarski(A_82, B_83))), inference(resolution, [status(thm)], [c_189, c_20])).
% 38.65/29.10  tff(c_52, plain, (v13_waybel_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_146])).
% 38.65/29.10  tff(c_76, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_146])).
% 38.65/29.10  tff(c_101, plain, (~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_76])).
% 38.65/29.10  tff(c_105, plain, (v1_xboole_0('#skF_6') | ~m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_22, c_101])).
% 38.65/29.10  tff(c_108, plain, (~m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_56, c_105])).
% 38.65/29.10  tff(c_58, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_146])).
% 38.65/29.10  tff(c_70, plain, (r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 38.65/29.10  tff(c_102, plain, (~v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_70])).
% 38.65/29.10  tff(c_142, plain, (![B_80, A_81]: (v1_subset_1(B_80, A_81) | B_80=A_81 | ~m1_subset_1(B_80, k1_zfmisc_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_117])).
% 38.65/29.10  tff(c_152, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5')) | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_50, c_142])).
% 38.65/29.10  tff(c_157, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_102, c_152])).
% 38.65/29.10  tff(c_30, plain, (![A_26]: (m1_subset_1(k3_yellow_0(A_26), u1_struct_0(A_26)) | ~l1_orders_2(A_26))), inference(cnfTransformation, [status(thm)], [f_77])).
% 38.65/29.10  tff(c_165, plain, (m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6') | ~l1_orders_2('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_157, c_30])).
% 38.65/29.10  tff(c_169, plain, (m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_165])).
% 38.65/29.10  tff(c_171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_108, c_169])).
% 38.65/29.10  tff(c_172, plain, (r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_70])).
% 38.65/29.10  tff(c_180, plain, $false, inference(negUnitSimplification, [status(thm)], [c_101, c_172])).
% 38.65/29.10  tff(c_182, plain, (r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_76])).
% 38.65/29.10  tff(c_68, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_146])).
% 38.65/29.10  tff(c_62, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_146])).
% 38.65/29.10  tff(c_60, plain, (v1_yellow_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_146])).
% 38.65/29.10  tff(c_327, plain, (![A_106]: (m1_subset_1(A_106, u1_struct_0('#skF_5')) | ~r2_hidden(A_106, '#skF_6'))), inference(resolution, [status(thm)], [c_50, c_309])).
% 38.65/29.10  tff(c_32, plain, (![A_27, B_29]: (r1_orders_2(A_27, k3_yellow_0(A_27), B_29) | ~m1_subset_1(B_29, u1_struct_0(A_27)) | ~l1_orders_2(A_27) | ~v1_yellow_0(A_27) | ~v5_orders_2(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_91])).
% 38.65/29.10  tff(c_1695, plain, (![D_240, B_241, A_242, C_243]: (r2_hidden(D_240, B_241) | ~r1_orders_2(A_242, C_243, D_240) | ~r2_hidden(C_243, B_241) | ~m1_subset_1(D_240, u1_struct_0(A_242)) | ~m1_subset_1(C_243, u1_struct_0(A_242)) | ~v13_waybel_0(B_241, A_242) | ~m1_subset_1(B_241, k1_zfmisc_1(u1_struct_0(A_242))) | ~l1_orders_2(A_242))), inference(cnfTransformation, [status(thm)], [f_110])).
% 38.65/29.10  tff(c_4460, plain, (![B_430, B_431, A_432]: (r2_hidden(B_430, B_431) | ~r2_hidden(k3_yellow_0(A_432), B_431) | ~m1_subset_1(k3_yellow_0(A_432), u1_struct_0(A_432)) | ~v13_waybel_0(B_431, A_432) | ~m1_subset_1(B_431, k1_zfmisc_1(u1_struct_0(A_432))) | ~m1_subset_1(B_430, u1_struct_0(A_432)) | ~l1_orders_2(A_432) | ~v1_yellow_0(A_432) | ~v5_orders_2(A_432) | v2_struct_0(A_432))), inference(resolution, [status(thm)], [c_32, c_1695])).
% 38.65/29.10  tff(c_4471, plain, (![B_430, B_431]: (r2_hidden(B_430, B_431) | ~r2_hidden(k3_yellow_0('#skF_5'), B_431) | ~v13_waybel_0(B_431, '#skF_5') | ~m1_subset_1(B_431, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_430, u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v1_yellow_0('#skF_5') | ~v5_orders_2('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_327, c_4460])).
% 38.65/29.10  tff(c_4494, plain, (![B_430, B_431]: (r2_hidden(B_430, B_431) | ~r2_hidden(k3_yellow_0('#skF_5'), B_431) | ~v13_waybel_0(B_431, '#skF_5') | ~m1_subset_1(B_431, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_430, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_62, c_60, c_58, c_4471])).
% 38.65/29.10  tff(c_4615, plain, (![B_442, B_443]: (r2_hidden(B_442, B_443) | ~r2_hidden(k3_yellow_0('#skF_5'), B_443) | ~v13_waybel_0(B_443, '#skF_5') | ~m1_subset_1(B_443, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_442, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_68, c_4494])).
% 38.65/29.10  tff(c_4665, plain, (![B_442]: (r2_hidden(B_442, '#skF_6') | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v13_waybel_0('#skF_6', '#skF_5') | ~m1_subset_1(B_442, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_50, c_4615])).
% 38.65/29.10  tff(c_4685, plain, (![B_444]: (r2_hidden(B_444, '#skF_6') | ~m1_subset_1(B_444, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_182, c_4665])).
% 38.65/29.10  tff(c_4988, plain, (![B_454]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_454), '#skF_6') | r1_tarski(u1_struct_0('#skF_5'), B_454))), inference(resolution, [status(thm)], [c_193, c_4685])).
% 38.65/29.10  tff(c_4998, plain, (r1_tarski(u1_struct_0('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_4988, c_4])).
% 38.65/29.10  tff(c_5008, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2668, c_2668, c_4998])).
% 38.65/29.10  tff(c_5010, plain, (r1_tarski(u1_struct_0('#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_2667])).
% 38.65/29.10  tff(c_1309, plain, (![A_209, B_210, C_211]: (r2_hidden('#skF_2'(A_209, B_210, C_211), B_210) | r2_hidden('#skF_2'(A_209, B_210, C_211), C_211) | C_211=B_210 | ~m1_subset_1(C_211, k1_zfmisc_1(A_209)) | ~m1_subset_1(B_210, k1_zfmisc_1(A_209)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 38.65/29.10  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 38.65/29.10  tff(c_1360, plain, (![A_209, B_210, C_211, B_2]: (r2_hidden('#skF_2'(A_209, B_210, C_211), B_2) | ~r1_tarski(C_211, B_2) | r2_hidden('#skF_2'(A_209, B_210, C_211), B_210) | C_211=B_210 | ~m1_subset_1(C_211, k1_zfmisc_1(A_209)) | ~m1_subset_1(B_210, k1_zfmisc_1(A_209)))), inference(resolution, [status(thm)], [c_1309, c_2])).
% 38.65/29.10  tff(c_5894, plain, (![C_211, B_2, A_209]: (~r1_tarski(C_211, B_2) | C_211=B_2 | ~m1_subset_1(C_211, k1_zfmisc_1(A_209)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_209)) | r2_hidden('#skF_2'(A_209, B_2, C_211), B_2))), inference(factorization, [status(thm), theory('equality')], [c_1360])).
% 38.65/29.10  tff(c_1353, plain, (![A_209, B_210, C_211, B_2]: (r2_hidden('#skF_2'(A_209, B_210, C_211), B_2) | ~r1_tarski(B_210, B_2) | r2_hidden('#skF_2'(A_209, B_210, C_211), C_211) | C_211=B_210 | ~m1_subset_1(C_211, k1_zfmisc_1(A_209)) | ~m1_subset_1(B_210, k1_zfmisc_1(A_209)))), inference(resolution, [status(thm)], [c_1309, c_2])).
% 38.65/29.10  tff(c_10598, plain, (![B_670, C_671, A_672]: (~r1_tarski(B_670, C_671) | C_671=B_670 | ~m1_subset_1(C_671, k1_zfmisc_1(A_672)) | ~m1_subset_1(B_670, k1_zfmisc_1(A_672)) | r2_hidden('#skF_2'(A_672, B_670, C_671), C_671))), inference(factorization, [status(thm), theory('equality')], [c_1353])).
% 38.65/29.10  tff(c_12, plain, (![A_10, B_11, C_15]: (~r2_hidden('#skF_2'(A_10, B_11, C_15), C_15) | ~r2_hidden('#skF_2'(A_10, B_11, C_15), B_11) | C_15=B_11 | ~m1_subset_1(C_15, k1_zfmisc_1(A_10)) | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 38.65/29.10  tff(c_52180, plain, (![A_1520, B_1521, C_1522]: (~r2_hidden('#skF_2'(A_1520, B_1521, C_1522), B_1521) | ~r1_tarski(B_1521, C_1522) | C_1522=B_1521 | ~m1_subset_1(C_1522, k1_zfmisc_1(A_1520)) | ~m1_subset_1(B_1521, k1_zfmisc_1(A_1520)))), inference(resolution, [status(thm)], [c_10598, c_12])).
% 38.65/29.10  tff(c_52464, plain, (![B_1523, C_1524, A_1525]: (~r1_tarski(B_1523, C_1524) | ~r1_tarski(C_1524, B_1523) | C_1524=B_1523 | ~m1_subset_1(C_1524, k1_zfmisc_1(A_1525)) | ~m1_subset_1(B_1523, k1_zfmisc_1(A_1525)))), inference(resolution, [status(thm)], [c_5894, c_52180])).
% 38.65/29.10  tff(c_52554, plain, (![A_1525]: (~r1_tarski(u1_struct_0('#skF_5'), '#skF_6') | u1_struct_0('#skF_5')='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_1525)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1525)))), inference(resolution, [status(thm)], [c_88, c_52464])).
% 38.65/29.10  tff(c_52606, plain, (![A_1525]: (u1_struct_0('#skF_5')='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_1525)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1525)))), inference(demodulation, [status(thm), theory('equality')], [c_5010, c_52554])).
% 38.65/29.10  tff(c_52608, plain, (![A_1526]: (~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_1526)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1526)))), inference(splitLeft, [status(thm)], [c_52606])).
% 38.65/29.10  tff(c_52614, plain, (![B_1527]: (~m1_subset_1('#skF_6', k1_zfmisc_1(B_1527)) | ~r1_tarski(u1_struct_0('#skF_5'), B_1527))), inference(resolution, [status(thm)], [c_26, c_52608])).
% 38.65/29.10  tff(c_52631, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_tarski(u1_struct_0('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_595, c_52614])).
% 38.65/29.10  tff(c_52645, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5010, c_50, c_52631])).
% 38.65/29.10  tff(c_52646, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_52606])).
% 38.65/29.10  tff(c_350, plain, (![A_115, B_116]: (r1_tarski(A_115, B_116) | v1_xboole_0(B_116) | ~m1_subset_1('#skF_1'(A_115, B_116), B_116))), inference(resolution, [status(thm)], [c_22, c_194])).
% 38.65/29.10  tff(c_363, plain, (![A_115]: (r1_tarski(A_115, u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5')) | ~r2_hidden('#skF_1'(A_115, u1_struct_0('#skF_5')), '#skF_6'))), inference(resolution, [status(thm)], [c_327, c_350])).
% 38.65/29.10  tff(c_379, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_363])).
% 38.65/29.10  tff(c_53078, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_52646, c_379])).
% 38.65/29.10  tff(c_53092, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_53078])).
% 38.65/29.10  tff(c_53094, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_363])).
% 38.65/29.10  tff(c_53252, plain, (![A_1553, B_1554, B_1555]: (r2_hidden('#skF_1'(A_1553, B_1554), B_1555) | ~r1_tarski(A_1553, B_1555) | r1_tarski(A_1553, B_1554))), inference(resolution, [status(thm)], [c_6, c_205])).
% 38.65/29.10  tff(c_53093, plain, (![A_115]: (r1_tarski(A_115, u1_struct_0('#skF_5')) | ~r2_hidden('#skF_1'(A_115, u1_struct_0('#skF_5')), '#skF_6'))), inference(splitRight, [status(thm)], [c_363])).
% 38.65/29.10  tff(c_53276, plain, (![A_1556]: (~r1_tarski(A_1556, '#skF_6') | r1_tarski(A_1556, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_53252, c_53093])).
% 38.65/29.10  tff(c_214, plain, (![A_19, B_87, B_20]: (r2_hidden(A_19, B_87) | ~r1_tarski(B_20, B_87) | v1_xboole_0(B_20) | ~m1_subset_1(A_19, B_20))), inference(resolution, [status(thm)], [c_22, c_205])).
% 38.65/29.10  tff(c_53797, plain, (![A_1606, A_1607]: (r2_hidden(A_1606, u1_struct_0('#skF_5')) | v1_xboole_0(A_1607) | ~m1_subset_1(A_1606, A_1607) | ~r1_tarski(A_1607, '#skF_6'))), inference(resolution, [status(thm)], [c_53276, c_214])).
% 38.65/29.10  tff(c_53813, plain, (![A_106]: (r2_hidden(A_106, u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5')) | ~r1_tarski(u1_struct_0('#skF_5'), '#skF_6') | ~r2_hidden(A_106, '#skF_6'))), inference(resolution, [status(thm)], [c_327, c_53797])).
% 38.65/29.10  tff(c_53840, plain, (![A_106]: (r2_hidden(A_106, u1_struct_0('#skF_5')) | ~r1_tarski(u1_struct_0('#skF_5'), '#skF_6') | ~r2_hidden(A_106, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_53094, c_53813])).
% 38.65/29.10  tff(c_53853, plain, (~r1_tarski(u1_struct_0('#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_53840])).
% 38.65/29.10  tff(c_54444, plain, (![D_1653, B_1654, A_1655, C_1656]: (r2_hidden(D_1653, B_1654) | ~r1_orders_2(A_1655, C_1656, D_1653) | ~r2_hidden(C_1656, B_1654) | ~m1_subset_1(D_1653, u1_struct_0(A_1655)) | ~m1_subset_1(C_1656, u1_struct_0(A_1655)) | ~v13_waybel_0(B_1654, A_1655) | ~m1_subset_1(B_1654, k1_zfmisc_1(u1_struct_0(A_1655))) | ~l1_orders_2(A_1655))), inference(cnfTransformation, [status(thm)], [f_110])).
% 38.65/29.10  tff(c_57184, plain, (![B_1852, B_1853, A_1854]: (r2_hidden(B_1852, B_1853) | ~r2_hidden(k3_yellow_0(A_1854), B_1853) | ~m1_subset_1(k3_yellow_0(A_1854), u1_struct_0(A_1854)) | ~v13_waybel_0(B_1853, A_1854) | ~m1_subset_1(B_1853, k1_zfmisc_1(u1_struct_0(A_1854))) | ~m1_subset_1(B_1852, u1_struct_0(A_1854)) | ~l1_orders_2(A_1854) | ~v1_yellow_0(A_1854) | ~v5_orders_2(A_1854) | v2_struct_0(A_1854))), inference(resolution, [status(thm)], [c_32, c_54444])).
% 38.65/29.10  tff(c_57195, plain, (![B_1852, B_1853]: (r2_hidden(B_1852, B_1853) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1853) | ~v13_waybel_0(B_1853, '#skF_5') | ~m1_subset_1(B_1853, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_1852, u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v1_yellow_0('#skF_5') | ~v5_orders_2('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_327, c_57184])).
% 38.65/29.10  tff(c_57218, plain, (![B_1852, B_1853]: (r2_hidden(B_1852, B_1853) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1853) | ~v13_waybel_0(B_1853, '#skF_5') | ~m1_subset_1(B_1853, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_1852, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_62, c_60, c_58, c_57195])).
% 38.65/29.10  tff(c_57343, plain, (![B_1864, B_1865]: (r2_hidden(B_1864, B_1865) | ~r2_hidden(k3_yellow_0('#skF_5'), B_1865) | ~v13_waybel_0(B_1865, '#skF_5') | ~m1_subset_1(B_1865, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_1864, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_68, c_57218])).
% 38.65/29.10  tff(c_57393, plain, (![B_1864]: (r2_hidden(B_1864, '#skF_6') | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v13_waybel_0('#skF_6', '#skF_5') | ~m1_subset_1(B_1864, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_50, c_57343])).
% 38.65/29.10  tff(c_57413, plain, (![B_1866]: (r2_hidden(B_1866, '#skF_6') | ~m1_subset_1(B_1866, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_182, c_57393])).
% 38.65/29.10  tff(c_57736, plain, (![B_1876]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_1876), '#skF_6') | r1_tarski(u1_struct_0('#skF_5'), B_1876))), inference(resolution, [status(thm)], [c_193, c_57413])).
% 38.65/29.10  tff(c_57750, plain, (r1_tarski(u1_struct_0('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_57736, c_4])).
% 38.65/29.10  tff(c_57762, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53853, c_53853, c_57750])).
% 38.65/29.10  tff(c_57764, plain, (r1_tarski(u1_struct_0('#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_53840])).
% 38.65/29.10  tff(c_53270, plain, (![A_1553]: (~r1_tarski(A_1553, '#skF_6') | r1_tarski(A_1553, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_53252, c_53093])).
% 38.65/29.10  tff(c_58302, plain, (![A_1905, B_1906, C_1907]: (r2_hidden('#skF_2'(A_1905, B_1906, C_1907), B_1906) | r2_hidden('#skF_2'(A_1905, B_1906, C_1907), C_1907) | C_1907=B_1906 | ~m1_subset_1(C_1907, k1_zfmisc_1(A_1905)) | ~m1_subset_1(B_1906, k1_zfmisc_1(A_1905)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 38.65/29.10  tff(c_58343, plain, (![A_1905, B_1906, C_1907, B_2]: (r2_hidden('#skF_2'(A_1905, B_1906, C_1907), B_2) | ~r1_tarski(C_1907, B_2) | r2_hidden('#skF_2'(A_1905, B_1906, C_1907), B_1906) | C_1907=B_1906 | ~m1_subset_1(C_1907, k1_zfmisc_1(A_1905)) | ~m1_subset_1(B_1906, k1_zfmisc_1(A_1905)))), inference(resolution, [status(thm)], [c_58302, c_2])).
% 38.65/29.10  tff(c_61097, plain, (![C_1907, B_1906, A_1905]: (~r1_tarski(C_1907, B_1906) | C_1907=B_1906 | ~m1_subset_1(C_1907, k1_zfmisc_1(A_1905)) | ~m1_subset_1(B_1906, k1_zfmisc_1(A_1905)) | r2_hidden('#skF_2'(A_1905, B_1906, C_1907), B_1906))), inference(factorization, [status(thm), theory('equality')], [c_58343])).
% 38.65/29.10  tff(c_58337, plain, (![A_1905, B_1906, C_1907, B_2]: (r2_hidden('#skF_2'(A_1905, B_1906, C_1907), B_2) | ~r1_tarski(B_1906, B_2) | r2_hidden('#skF_2'(A_1905, B_1906, C_1907), C_1907) | C_1907=B_1906 | ~m1_subset_1(C_1907, k1_zfmisc_1(A_1905)) | ~m1_subset_1(B_1906, k1_zfmisc_1(A_1905)))), inference(resolution, [status(thm)], [c_58302, c_2])).
% 38.65/29.10  tff(c_66835, plain, (![B_2237, C_2238, A_2239]: (~r1_tarski(B_2237, C_2238) | C_2238=B_2237 | ~m1_subset_1(C_2238, k1_zfmisc_1(A_2239)) | ~m1_subset_1(B_2237, k1_zfmisc_1(A_2239)) | r2_hidden('#skF_2'(A_2239, B_2237, C_2238), C_2238))), inference(factorization, [status(thm), theory('equality')], [c_58337])).
% 38.65/29.10  tff(c_106692, plain, (![A_3075, B_3076, C_3077]: (~r2_hidden('#skF_2'(A_3075, B_3076, C_3077), B_3076) | ~r1_tarski(B_3076, C_3077) | C_3077=B_3076 | ~m1_subset_1(C_3077, k1_zfmisc_1(A_3075)) | ~m1_subset_1(B_3076, k1_zfmisc_1(A_3075)))), inference(resolution, [status(thm)], [c_66835, c_12])).
% 38.65/29.10  tff(c_106969, plain, (![B_3078, C_3079, A_3080]: (~r1_tarski(B_3078, C_3079) | ~r1_tarski(C_3079, B_3078) | C_3079=B_3078 | ~m1_subset_1(C_3079, k1_zfmisc_1(A_3080)) | ~m1_subset_1(B_3078, k1_zfmisc_1(A_3080)))), inference(resolution, [status(thm)], [c_61097, c_106692])).
% 38.65/29.10  tff(c_107061, plain, (![A_3080]: (~r1_tarski(u1_struct_0('#skF_5'), '#skF_6') | u1_struct_0('#skF_5')='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_3080)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_3080)))), inference(resolution, [status(thm)], [c_88, c_106969])).
% 38.65/29.10  tff(c_107114, plain, (![A_3080]: (u1_struct_0('#skF_5')='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_3080)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_3080)))), inference(demodulation, [status(thm), theory('equality')], [c_57764, c_107061])).
% 38.65/29.10  tff(c_107116, plain, (![A_3081]: (~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_3081)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_3081)))), inference(splitLeft, [status(thm)], [c_107114])).
% 38.65/29.10  tff(c_107122, plain, (![B_3082]: (~m1_subset_1('#skF_6', k1_zfmisc_1(B_3082)) | ~r1_tarski(u1_struct_0('#skF_5'), B_3082))), inference(resolution, [status(thm)], [c_26, c_107116])).
% 38.65/29.10  tff(c_107139, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_tarski(u1_struct_0('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_53270, c_107122])).
% 38.65/29.10  tff(c_107153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_57764, c_50, c_107139])).
% 38.65/29.10  tff(c_107154, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_107114])).
% 38.65/29.10  tff(c_181, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_76])).
% 38.65/29.10  tff(c_107594, plain, (v1_subset_1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_107154, c_181])).
% 38.65/29.10  tff(c_107606, plain, $false, inference(negUnitSimplification, [status(thm)], [c_216, c_107594])).
% 38.65/29.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 38.65/29.10  
% 38.65/29.10  Inference rules
% 38.65/29.10  ----------------------
% 38.65/29.10  #Ref     : 0
% 38.65/29.10  #Sup     : 26020
% 38.65/29.10  #Fact    : 82
% 38.65/29.10  #Define  : 0
% 38.65/29.10  #Split   : 86
% 38.65/29.10  #Chain   : 0
% 38.65/29.10  #Close   : 0
% 38.65/29.10  
% 38.65/29.10  Ordering : KBO
% 38.65/29.10  
% 38.65/29.10  Simplification rules
% 38.65/29.10  ----------------------
% 38.65/29.10  #Subsume      : 7473
% 38.65/29.10  #Demod        : 3692
% 38.65/29.10  #Tautology    : 905
% 38.65/29.10  #SimpNegUnit  : 317
% 38.65/29.10  #BackRed      : 588
% 38.65/29.10  
% 38.65/29.10  #Partial instantiations: 0
% 38.65/29.10  #Strategies tried      : 1
% 38.65/29.10  
% 38.65/29.10  Timing (in seconds)
% 38.65/29.10  ----------------------
% 38.94/29.10  Preprocessing        : 0.33
% 38.94/29.10  Parsing              : 0.19
% 38.94/29.10  CNF conversion       : 0.03
% 38.94/29.10  Main loop            : 27.98
% 38.94/29.10  Inferencing          : 3.04
% 38.94/29.10  Reduction            : 4.78
% 38.94/29.10  Demodulation         : 3.10
% 38.94/29.10  BG Simplification    : 0.36
% 38.94/29.10  Subsumption          : 18.32
% 38.94/29.10  Abstraction          : 0.54
% 38.94/29.10  MUC search           : 0.00
% 38.94/29.10  Cooper               : 0.00
% 38.94/29.10  Total                : 28.37
% 38.94/29.10  Index Insertion      : 0.00
% 38.94/29.10  Index Deletion       : 0.00
% 38.94/29.10  Index Matching       : 0.00
% 38.94/29.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
