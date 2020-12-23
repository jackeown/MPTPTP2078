%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:03 EST 2020

% Result     : Theorem 10.81s
% Output     : CNFRefutation 10.86s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 360 expanded)
%              Number of leaves         :   39 ( 138 expanded)
%              Depth                    :   16
%              Number of atoms          :  231 (1518 expanded)
%              Number of equality atoms :   25 (  66 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k3_yellow_0 > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_5 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(v1_yellow_0,type,(
    v1_yellow_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_53,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_63,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_142,negated_conjecture,(
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

tff(f_51,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_113,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(k3_yellow_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_87,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,k3_yellow_0(A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_yellow_0)).

tff(f_106,axiom,(
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

tff(c_22,plain,(
    ! [A_10] : k2_subset_1(A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_26,plain,(
    ! [A_15] : ~ v1_subset_1(k2_subset_1(A_15),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_77,plain,(
    ! [A_15] : ~ v1_subset_1(A_15,A_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_26])).

tff(c_50,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_76,plain,
    ( v1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ r2_hidden(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_111,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_113,plain,(
    ! [B_61,A_62] :
      ( r2_hidden(B_61,A_62)
      | ~ m1_subset_1(B_61,A_62)
      | v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_116,plain,
    ( ~ m1_subset_1(k3_yellow_0('#skF_6'),'#skF_7')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_113,c_111])).

tff(c_122,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_116])).

tff(c_58,plain,(
    l1_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_70,plain,
    ( r2_hidden(k3_yellow_0('#skF_6'),'#skF_7')
    | ~ v1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_112,plain,(
    ~ v1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_137,plain,(
    ! [B_65,A_66] :
      ( v1_subset_1(B_65,A_66)
      | B_65 = A_66
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_144,plain,
    ( v1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | u1_struct_0('#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_50,c_137])).

tff(c_148,plain,(
    u1_struct_0('#skF_6') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_144])).

tff(c_30,plain,(
    ! [A_19] :
      ( m1_subset_1(k3_yellow_0(A_19),u1_struct_0(A_19))
      | ~ l1_orders_2(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_155,plain,
    ( m1_subset_1(k3_yellow_0('#skF_6'),'#skF_7')
    | ~ l1_orders_2('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_30])).

tff(c_159,plain,(
    m1_subset_1(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_155])).

tff(c_161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_159])).

tff(c_162,plain,(
    r2_hidden(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_162])).

tff(c_166,plain,(
    r2_hidden(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_245,plain,(
    ! [C_79,A_80,B_81] :
      ( r2_hidden(C_79,A_80)
      | ~ r2_hidden(C_79,B_81)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_255,plain,(
    ! [A_82] :
      ( r2_hidden(k3_yellow_0('#skF_6'),A_82)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_82)) ) ),
    inference(resolution,[status(thm)],[c_166,c_245])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_267,plain,(
    ! [A_83] :
      ( ~ v1_xboole_0(A_83)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_83)) ) ),
    inference(resolution,[status(thm)],[c_255,c_2])).

tff(c_275,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_50,c_267])).

tff(c_325,plain,(
    ! [A_92,B_93] :
      ( r2_hidden('#skF_2'(A_92,B_93),B_93)
      | r2_hidden('#skF_3'(A_92,B_93),A_92)
      | B_93 = A_92 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_24,plain,(
    ! [C_14,A_11,B_12] :
      ( r2_hidden(C_14,A_11)
      | ~ r2_hidden(C_14,B_12)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_3046,plain,(
    ! [A_257,B_258,A_259] :
      ( r2_hidden('#skF_2'(A_257,B_258),A_259)
      | ~ m1_subset_1(B_258,k1_zfmisc_1(A_259))
      | r2_hidden('#skF_3'(A_257,B_258),A_257)
      | B_258 = A_257 ) ),
    inference(resolution,[status(thm)],[c_325,c_24])).

tff(c_14,plain,(
    ! [B_9,A_8] :
      ( m1_subset_1(B_9,A_8)
      | ~ r2_hidden(B_9,A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8809,plain,(
    ! [A_359,B_360,A_361] :
      ( m1_subset_1('#skF_3'(A_359,B_360),A_359)
      | v1_xboole_0(A_359)
      | r2_hidden('#skF_2'(A_359,B_360),A_361)
      | ~ m1_subset_1(B_360,k1_zfmisc_1(A_361))
      | B_360 = A_359 ) ),
    inference(resolution,[status(thm)],[c_3046,c_14])).

tff(c_515,plain,(
    ! [A_114,B_115] :
      ( ~ r2_hidden('#skF_2'(A_114,B_115),A_114)
      | r2_hidden('#skF_3'(A_114,B_115),A_114)
      | B_115 = A_114 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_536,plain,(
    ! [A_114,B_115] :
      ( m1_subset_1('#skF_3'(A_114,B_115),A_114)
      | v1_xboole_0(A_114)
      | ~ r2_hidden('#skF_2'(A_114,B_115),A_114)
      | B_115 = A_114 ) ),
    inference(resolution,[status(thm)],[c_515,c_14])).

tff(c_10131,plain,(
    ! [A_379,B_380] :
      ( m1_subset_1('#skF_3'(A_379,B_380),A_379)
      | v1_xboole_0(A_379)
      | ~ m1_subset_1(B_380,k1_zfmisc_1(A_379))
      | B_380 = A_379 ) ),
    inference(resolution,[status(thm)],[c_8809,c_536])).

tff(c_52,plain,(
    v13_waybel_0('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_62,plain,(
    v5_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_60,plain,(
    v1_yellow_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_228,plain,(
    ! [A_75,C_76,B_77] :
      ( m1_subset_1(A_75,C_76)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(C_76))
      | ~ r2_hidden(A_75,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_239,plain,(
    ! [A_75] :
      ( m1_subset_1(A_75,u1_struct_0('#skF_6'))
      | ~ r2_hidden(A_75,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_50,c_228])).

tff(c_32,plain,(
    ! [A_20,B_22] :
      ( r1_orders_2(A_20,k3_yellow_0(A_20),B_22)
      | ~ m1_subset_1(B_22,u1_struct_0(A_20))
      | ~ l1_orders_2(A_20)
      | ~ v1_yellow_0(A_20)
      | ~ v5_orders_2(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2281,plain,(
    ! [D_225,B_226,A_227,C_228] :
      ( r2_hidden(D_225,B_226)
      | ~ r1_orders_2(A_227,C_228,D_225)
      | ~ r2_hidden(C_228,B_226)
      | ~ m1_subset_1(D_225,u1_struct_0(A_227))
      | ~ m1_subset_1(C_228,u1_struct_0(A_227))
      | ~ v13_waybel_0(B_226,A_227)
      | ~ m1_subset_1(B_226,k1_zfmisc_1(u1_struct_0(A_227)))
      | ~ l1_orders_2(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_6234,plain,(
    ! [B_308,B_309,A_310] :
      ( r2_hidden(B_308,B_309)
      | ~ r2_hidden(k3_yellow_0(A_310),B_309)
      | ~ m1_subset_1(k3_yellow_0(A_310),u1_struct_0(A_310))
      | ~ v13_waybel_0(B_309,A_310)
      | ~ m1_subset_1(B_309,k1_zfmisc_1(u1_struct_0(A_310)))
      | ~ m1_subset_1(B_308,u1_struct_0(A_310))
      | ~ l1_orders_2(A_310)
      | ~ v1_yellow_0(A_310)
      | ~ v5_orders_2(A_310)
      | v2_struct_0(A_310) ) ),
    inference(resolution,[status(thm)],[c_32,c_2281])).

tff(c_6243,plain,(
    ! [B_308,B_309] :
      ( r2_hidden(B_308,B_309)
      | ~ r2_hidden(k3_yellow_0('#skF_6'),B_309)
      | ~ v13_waybel_0(B_309,'#skF_6')
      | ~ m1_subset_1(B_309,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(B_308,u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | ~ v1_yellow_0('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ r2_hidden(k3_yellow_0('#skF_6'),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_239,c_6234])).

tff(c_6259,plain,(
    ! [B_308,B_309] :
      ( r2_hidden(B_308,B_309)
      | ~ r2_hidden(k3_yellow_0('#skF_6'),B_309)
      | ~ v13_waybel_0(B_309,'#skF_6')
      | ~ m1_subset_1(B_309,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(B_308,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_62,c_60,c_58,c_6243])).

tff(c_7176,plain,(
    ! [B_338,B_339] :
      ( r2_hidden(B_338,B_339)
      | ~ r2_hidden(k3_yellow_0('#skF_6'),B_339)
      | ~ v13_waybel_0(B_339,'#skF_6')
      | ~ m1_subset_1(B_339,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(B_338,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_6259])).

tff(c_7242,plain,(
    ! [B_338] :
      ( r2_hidden(B_338,'#skF_7')
      | ~ r2_hidden(k3_yellow_0('#skF_6'),'#skF_7')
      | ~ v13_waybel_0('#skF_7','#skF_6')
      | ~ m1_subset_1(B_338,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_50,c_7176])).

tff(c_7292,plain,(
    ! [B_338] :
      ( r2_hidden(B_338,'#skF_7')
      | ~ m1_subset_1(B_338,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_166,c_7242])).

tff(c_10150,plain,(
    ! [B_380] :
      ( r2_hidden('#skF_3'(u1_struct_0('#skF_6'),B_380),'#skF_7')
      | v1_xboole_0(u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_380,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | u1_struct_0('#skF_6') = B_380 ) ),
    inference(resolution,[status(thm)],[c_10131,c_7292])).

tff(c_13771,plain,(
    ! [B_434] :
      ( r2_hidden('#skF_3'(u1_struct_0('#skF_6'),B_434),'#skF_7')
      | ~ m1_subset_1(B_434,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | u1_struct_0('#skF_6') = B_434 ) ),
    inference(negUnitSimplification,[status(thm)],[c_275,c_10150])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),B_6)
      | ~ r2_hidden('#skF_3'(A_5,B_6),B_6)
      | B_6 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_13786,plain,
    ( r2_hidden('#skF_2'(u1_struct_0('#skF_6'),'#skF_7'),'#skF_7')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6')))
    | u1_struct_0('#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_13771,c_8])).

tff(c_13807,plain,
    ( r2_hidden('#skF_2'(u1_struct_0('#skF_6'),'#skF_7'),'#skF_7')
    | u1_struct_0('#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_13786])).

tff(c_13862,plain,(
    u1_struct_0('#skF_6') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_13807])).

tff(c_165,plain,(
    v1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_13920,plain,(
    v1_subset_1('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13862,c_165])).

tff(c_13927,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_13920])).

tff(c_13929,plain,(
    u1_struct_0('#skF_6') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_13807])).

tff(c_13928,plain,(
    r2_hidden('#skF_2'(u1_struct_0('#skF_6'),'#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_13807])).

tff(c_14075,plain,
    ( m1_subset_1('#skF_2'(u1_struct_0('#skF_6'),'#skF_7'),'#skF_7')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_13928,c_14])).

tff(c_14082,plain,(
    m1_subset_1('#skF_2'(u1_struct_0('#skF_6'),'#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_14075])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( r2_hidden(B_9,A_8)
      | ~ m1_subset_1(B_9,A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_543,plain,(
    ! [B_117,A_118,A_119] :
      ( r2_hidden(B_117,A_118)
      | ~ m1_subset_1(A_119,k1_zfmisc_1(A_118))
      | ~ m1_subset_1(B_117,A_119)
      | v1_xboole_0(A_119) ) ),
    inference(resolution,[status(thm)],[c_16,c_245])).

tff(c_560,plain,(
    ! [B_117] :
      ( r2_hidden(B_117,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_117,'#skF_7')
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_50,c_543])).

tff(c_569,plain,(
    ! [B_120] :
      ( r2_hidden(B_120,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_120,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_560])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),A_5)
      | ~ r2_hidden('#skF_3'(A_5,B_6),B_6)
      | B_6 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_586,plain,(
    ! [B_6] :
      ( ~ r2_hidden('#skF_3'(u1_struct_0('#skF_6'),B_6),B_6)
      | u1_struct_0('#skF_6') = B_6
      | ~ m1_subset_1('#skF_2'(u1_struct_0('#skF_6'),B_6),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_569,c_6])).

tff(c_13782,plain,
    ( ~ m1_subset_1('#skF_2'(u1_struct_0('#skF_6'),'#skF_7'),'#skF_7')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6')))
    | u1_struct_0('#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_13771,c_586])).

tff(c_13804,plain,
    ( ~ m1_subset_1('#skF_2'(u1_struct_0('#skF_6'),'#skF_7'),'#skF_7')
    | u1_struct_0('#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_13782])).

tff(c_14089,plain,(
    u1_struct_0('#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14082,c_13804])).

tff(c_14090,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13929,c_14089])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:24:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.81/3.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.81/3.95  
% 10.81/3.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.86/3.95  %$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k3_yellow_0 > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_5 > #skF_4
% 10.86/3.95  
% 10.86/3.95  %Foreground sorts:
% 10.86/3.95  
% 10.86/3.95  
% 10.86/3.95  %Background operators:
% 10.86/3.95  
% 10.86/3.95  
% 10.86/3.95  %Foreground operators:
% 10.86/3.95  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 10.86/3.95  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 10.86/3.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.86/3.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.86/3.95  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 10.86/3.95  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.86/3.95  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 10.86/3.95  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 10.86/3.95  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 10.86/3.95  tff('#skF_7', type, '#skF_7': $i).
% 10.86/3.95  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 10.86/3.95  tff('#skF_6', type, '#skF_6': $i).
% 10.86/3.95  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 10.86/3.95  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 10.86/3.95  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.86/3.95  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 10.86/3.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.86/3.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.86/3.95  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.86/3.95  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 10.86/3.95  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.86/3.95  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 10.86/3.95  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.86/3.95  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 10.86/3.95  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 10.86/3.95  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 10.86/3.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.86/3.95  
% 10.86/3.97  tff(f_53, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 10.86/3.97  tff(f_63, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_subset_1)).
% 10.86/3.97  tff(f_142, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_subset_1(B, u1_struct_0(A)) <=> ~r2_hidden(k3_yellow_0(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_7)).
% 10.86/3.97  tff(f_51, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 10.86/3.97  tff(f_113, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 10.86/3.97  tff(f_73, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(k3_yellow_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow_0)).
% 10.86/3.97  tff(f_60, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 10.86/3.97  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 10.86/3.97  tff(f_38, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 10.86/3.97  tff(f_69, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 10.86/3.97  tff(f_87, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, k3_yellow_0(A), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_yellow_0)).
% 10.86/3.97  tff(f_106, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v13_waybel_0(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r1_orders_2(A, C, D)) => r2_hidden(D, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_waybel_0)).
% 10.86/3.97  tff(c_22, plain, (![A_10]: (k2_subset_1(A_10)=A_10)), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.86/3.97  tff(c_26, plain, (![A_15]: (~v1_subset_1(k2_subset_1(A_15), A_15))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.86/3.97  tff(c_77, plain, (![A_15]: (~v1_subset_1(A_15, A_15))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_26])).
% 10.86/3.97  tff(c_50, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 10.86/3.97  tff(c_76, plain, (v1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~r2_hidden(k3_yellow_0('#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_142])).
% 10.86/3.97  tff(c_111, plain, (~r2_hidden(k3_yellow_0('#skF_6'), '#skF_7')), inference(splitLeft, [status(thm)], [c_76])).
% 10.86/3.97  tff(c_56, plain, (~v1_xboole_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_142])).
% 10.86/3.97  tff(c_113, plain, (![B_61, A_62]: (r2_hidden(B_61, A_62) | ~m1_subset_1(B_61, A_62) | v1_xboole_0(A_62))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.86/3.97  tff(c_116, plain, (~m1_subset_1(k3_yellow_0('#skF_6'), '#skF_7') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_113, c_111])).
% 10.86/3.97  tff(c_122, plain, (~m1_subset_1(k3_yellow_0('#skF_6'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_56, c_116])).
% 10.86/3.97  tff(c_58, plain, (l1_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_142])).
% 10.86/3.97  tff(c_70, plain, (r2_hidden(k3_yellow_0('#skF_6'), '#skF_7') | ~v1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_142])).
% 10.86/3.97  tff(c_112, plain, (~v1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_70])).
% 10.86/3.97  tff(c_137, plain, (![B_65, A_66]: (v1_subset_1(B_65, A_66) | B_65=A_66 | ~m1_subset_1(B_65, k1_zfmisc_1(A_66)))), inference(cnfTransformation, [status(thm)], [f_113])).
% 10.86/3.97  tff(c_144, plain, (v1_subset_1('#skF_7', u1_struct_0('#skF_6')) | u1_struct_0('#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_50, c_137])).
% 10.86/3.97  tff(c_148, plain, (u1_struct_0('#skF_6')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_112, c_144])).
% 10.86/3.97  tff(c_30, plain, (![A_19]: (m1_subset_1(k3_yellow_0(A_19), u1_struct_0(A_19)) | ~l1_orders_2(A_19))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.86/3.97  tff(c_155, plain, (m1_subset_1(k3_yellow_0('#skF_6'), '#skF_7') | ~l1_orders_2('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_148, c_30])).
% 10.86/3.97  tff(c_159, plain, (m1_subset_1(k3_yellow_0('#skF_6'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_155])).
% 10.86/3.97  tff(c_161, plain, $false, inference(negUnitSimplification, [status(thm)], [c_122, c_159])).
% 10.86/3.97  tff(c_162, plain, (r2_hidden(k3_yellow_0('#skF_6'), '#skF_7')), inference(splitRight, [status(thm)], [c_70])).
% 10.86/3.97  tff(c_164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_111, c_162])).
% 10.86/3.97  tff(c_166, plain, (r2_hidden(k3_yellow_0('#skF_6'), '#skF_7')), inference(splitRight, [status(thm)], [c_76])).
% 10.86/3.97  tff(c_245, plain, (![C_79, A_80, B_81]: (r2_hidden(C_79, A_80) | ~r2_hidden(C_79, B_81) | ~m1_subset_1(B_81, k1_zfmisc_1(A_80)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.86/3.97  tff(c_255, plain, (![A_82]: (r2_hidden(k3_yellow_0('#skF_6'), A_82) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_82)))), inference(resolution, [status(thm)], [c_166, c_245])).
% 10.86/3.97  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.86/3.97  tff(c_267, plain, (![A_83]: (~v1_xboole_0(A_83) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_83)))), inference(resolution, [status(thm)], [c_255, c_2])).
% 10.86/3.97  tff(c_275, plain, (~v1_xboole_0(u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_50, c_267])).
% 10.86/3.97  tff(c_325, plain, (![A_92, B_93]: (r2_hidden('#skF_2'(A_92, B_93), B_93) | r2_hidden('#skF_3'(A_92, B_93), A_92) | B_93=A_92)), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.86/3.97  tff(c_24, plain, (![C_14, A_11, B_12]: (r2_hidden(C_14, A_11) | ~r2_hidden(C_14, B_12) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.86/3.97  tff(c_3046, plain, (![A_257, B_258, A_259]: (r2_hidden('#skF_2'(A_257, B_258), A_259) | ~m1_subset_1(B_258, k1_zfmisc_1(A_259)) | r2_hidden('#skF_3'(A_257, B_258), A_257) | B_258=A_257)), inference(resolution, [status(thm)], [c_325, c_24])).
% 10.86/3.97  tff(c_14, plain, (![B_9, A_8]: (m1_subset_1(B_9, A_8) | ~r2_hidden(B_9, A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.86/3.97  tff(c_8809, plain, (![A_359, B_360, A_361]: (m1_subset_1('#skF_3'(A_359, B_360), A_359) | v1_xboole_0(A_359) | r2_hidden('#skF_2'(A_359, B_360), A_361) | ~m1_subset_1(B_360, k1_zfmisc_1(A_361)) | B_360=A_359)), inference(resolution, [status(thm)], [c_3046, c_14])).
% 10.86/3.97  tff(c_515, plain, (![A_114, B_115]: (~r2_hidden('#skF_2'(A_114, B_115), A_114) | r2_hidden('#skF_3'(A_114, B_115), A_114) | B_115=A_114)), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.86/3.97  tff(c_536, plain, (![A_114, B_115]: (m1_subset_1('#skF_3'(A_114, B_115), A_114) | v1_xboole_0(A_114) | ~r2_hidden('#skF_2'(A_114, B_115), A_114) | B_115=A_114)), inference(resolution, [status(thm)], [c_515, c_14])).
% 10.86/3.97  tff(c_10131, plain, (![A_379, B_380]: (m1_subset_1('#skF_3'(A_379, B_380), A_379) | v1_xboole_0(A_379) | ~m1_subset_1(B_380, k1_zfmisc_1(A_379)) | B_380=A_379)), inference(resolution, [status(thm)], [c_8809, c_536])).
% 10.86/3.97  tff(c_52, plain, (v13_waybel_0('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_142])).
% 10.86/3.97  tff(c_68, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_142])).
% 10.86/3.97  tff(c_62, plain, (v5_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_142])).
% 10.86/3.97  tff(c_60, plain, (v1_yellow_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_142])).
% 10.86/3.97  tff(c_228, plain, (![A_75, C_76, B_77]: (m1_subset_1(A_75, C_76) | ~m1_subset_1(B_77, k1_zfmisc_1(C_76)) | ~r2_hidden(A_75, B_77))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.86/3.97  tff(c_239, plain, (![A_75]: (m1_subset_1(A_75, u1_struct_0('#skF_6')) | ~r2_hidden(A_75, '#skF_7'))), inference(resolution, [status(thm)], [c_50, c_228])).
% 10.86/3.97  tff(c_32, plain, (![A_20, B_22]: (r1_orders_2(A_20, k3_yellow_0(A_20), B_22) | ~m1_subset_1(B_22, u1_struct_0(A_20)) | ~l1_orders_2(A_20) | ~v1_yellow_0(A_20) | ~v5_orders_2(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.86/3.97  tff(c_2281, plain, (![D_225, B_226, A_227, C_228]: (r2_hidden(D_225, B_226) | ~r1_orders_2(A_227, C_228, D_225) | ~r2_hidden(C_228, B_226) | ~m1_subset_1(D_225, u1_struct_0(A_227)) | ~m1_subset_1(C_228, u1_struct_0(A_227)) | ~v13_waybel_0(B_226, A_227) | ~m1_subset_1(B_226, k1_zfmisc_1(u1_struct_0(A_227))) | ~l1_orders_2(A_227))), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.86/3.97  tff(c_6234, plain, (![B_308, B_309, A_310]: (r2_hidden(B_308, B_309) | ~r2_hidden(k3_yellow_0(A_310), B_309) | ~m1_subset_1(k3_yellow_0(A_310), u1_struct_0(A_310)) | ~v13_waybel_0(B_309, A_310) | ~m1_subset_1(B_309, k1_zfmisc_1(u1_struct_0(A_310))) | ~m1_subset_1(B_308, u1_struct_0(A_310)) | ~l1_orders_2(A_310) | ~v1_yellow_0(A_310) | ~v5_orders_2(A_310) | v2_struct_0(A_310))), inference(resolution, [status(thm)], [c_32, c_2281])).
% 10.86/3.97  tff(c_6243, plain, (![B_308, B_309]: (r2_hidden(B_308, B_309) | ~r2_hidden(k3_yellow_0('#skF_6'), B_309) | ~v13_waybel_0(B_309, '#skF_6') | ~m1_subset_1(B_309, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1(B_308, u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v1_yellow_0('#skF_6') | ~v5_orders_2('#skF_6') | v2_struct_0('#skF_6') | ~r2_hidden(k3_yellow_0('#skF_6'), '#skF_7'))), inference(resolution, [status(thm)], [c_239, c_6234])).
% 10.86/3.97  tff(c_6259, plain, (![B_308, B_309]: (r2_hidden(B_308, B_309) | ~r2_hidden(k3_yellow_0('#skF_6'), B_309) | ~v13_waybel_0(B_309, '#skF_6') | ~m1_subset_1(B_309, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1(B_308, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_166, c_62, c_60, c_58, c_6243])).
% 10.86/3.97  tff(c_7176, plain, (![B_338, B_339]: (r2_hidden(B_338, B_339) | ~r2_hidden(k3_yellow_0('#skF_6'), B_339) | ~v13_waybel_0(B_339, '#skF_6') | ~m1_subset_1(B_339, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1(B_338, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_68, c_6259])).
% 10.86/3.97  tff(c_7242, plain, (![B_338]: (r2_hidden(B_338, '#skF_7') | ~r2_hidden(k3_yellow_0('#skF_6'), '#skF_7') | ~v13_waybel_0('#skF_7', '#skF_6') | ~m1_subset_1(B_338, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_50, c_7176])).
% 10.86/3.97  tff(c_7292, plain, (![B_338]: (r2_hidden(B_338, '#skF_7') | ~m1_subset_1(B_338, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_166, c_7242])).
% 10.86/3.97  tff(c_10150, plain, (![B_380]: (r2_hidden('#skF_3'(u1_struct_0('#skF_6'), B_380), '#skF_7') | v1_xboole_0(u1_struct_0('#skF_6')) | ~m1_subset_1(B_380, k1_zfmisc_1(u1_struct_0('#skF_6'))) | u1_struct_0('#skF_6')=B_380)), inference(resolution, [status(thm)], [c_10131, c_7292])).
% 10.86/3.97  tff(c_13771, plain, (![B_434]: (r2_hidden('#skF_3'(u1_struct_0('#skF_6'), B_434), '#skF_7') | ~m1_subset_1(B_434, k1_zfmisc_1(u1_struct_0('#skF_6'))) | u1_struct_0('#skF_6')=B_434)), inference(negUnitSimplification, [status(thm)], [c_275, c_10150])).
% 10.86/3.97  tff(c_8, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), B_6) | ~r2_hidden('#skF_3'(A_5, B_6), B_6) | B_6=A_5)), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.86/3.97  tff(c_13786, plain, (r2_hidden('#skF_2'(u1_struct_0('#skF_6'), '#skF_7'), '#skF_7') | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6'))) | u1_struct_0('#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_13771, c_8])).
% 10.86/3.97  tff(c_13807, plain, (r2_hidden('#skF_2'(u1_struct_0('#skF_6'), '#skF_7'), '#skF_7') | u1_struct_0('#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_13786])).
% 10.86/3.97  tff(c_13862, plain, (u1_struct_0('#skF_6')='#skF_7'), inference(splitLeft, [status(thm)], [c_13807])).
% 10.86/3.97  tff(c_165, plain, (v1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_76])).
% 10.86/3.97  tff(c_13920, plain, (v1_subset_1('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_13862, c_165])).
% 10.86/3.97  tff(c_13927, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77, c_13920])).
% 10.86/3.97  tff(c_13929, plain, (u1_struct_0('#skF_6')!='#skF_7'), inference(splitRight, [status(thm)], [c_13807])).
% 10.86/3.97  tff(c_13928, plain, (r2_hidden('#skF_2'(u1_struct_0('#skF_6'), '#skF_7'), '#skF_7')), inference(splitRight, [status(thm)], [c_13807])).
% 10.86/3.97  tff(c_14075, plain, (m1_subset_1('#skF_2'(u1_struct_0('#skF_6'), '#skF_7'), '#skF_7') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_13928, c_14])).
% 10.86/3.97  tff(c_14082, plain, (m1_subset_1('#skF_2'(u1_struct_0('#skF_6'), '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_56, c_14075])).
% 10.86/3.97  tff(c_16, plain, (![B_9, A_8]: (r2_hidden(B_9, A_8) | ~m1_subset_1(B_9, A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.86/3.97  tff(c_543, plain, (![B_117, A_118, A_119]: (r2_hidden(B_117, A_118) | ~m1_subset_1(A_119, k1_zfmisc_1(A_118)) | ~m1_subset_1(B_117, A_119) | v1_xboole_0(A_119))), inference(resolution, [status(thm)], [c_16, c_245])).
% 10.86/3.97  tff(c_560, plain, (![B_117]: (r2_hidden(B_117, u1_struct_0('#skF_6')) | ~m1_subset_1(B_117, '#skF_7') | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_50, c_543])).
% 10.86/3.97  tff(c_569, plain, (![B_120]: (r2_hidden(B_120, u1_struct_0('#skF_6')) | ~m1_subset_1(B_120, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_56, c_560])).
% 10.86/3.97  tff(c_6, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), A_5) | ~r2_hidden('#skF_3'(A_5, B_6), B_6) | B_6=A_5)), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.86/3.97  tff(c_586, plain, (![B_6]: (~r2_hidden('#skF_3'(u1_struct_0('#skF_6'), B_6), B_6) | u1_struct_0('#skF_6')=B_6 | ~m1_subset_1('#skF_2'(u1_struct_0('#skF_6'), B_6), '#skF_7'))), inference(resolution, [status(thm)], [c_569, c_6])).
% 10.86/3.97  tff(c_13782, plain, (~m1_subset_1('#skF_2'(u1_struct_0('#skF_6'), '#skF_7'), '#skF_7') | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6'))) | u1_struct_0('#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_13771, c_586])).
% 10.86/3.97  tff(c_13804, plain, (~m1_subset_1('#skF_2'(u1_struct_0('#skF_6'), '#skF_7'), '#skF_7') | u1_struct_0('#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_13782])).
% 10.86/3.97  tff(c_14089, plain, (u1_struct_0('#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_14082, c_13804])).
% 10.86/3.97  tff(c_14090, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13929, c_14089])).
% 10.86/3.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.86/3.97  
% 10.86/3.97  Inference rules
% 10.86/3.97  ----------------------
% 10.86/3.97  #Ref     : 0
% 10.86/3.97  #Sup     : 3294
% 10.86/3.97  #Fact    : 4
% 10.86/3.97  #Define  : 0
% 10.86/3.97  #Split   : 15
% 10.86/3.97  #Chain   : 0
% 10.86/3.97  #Close   : 0
% 10.86/3.97  
% 10.86/3.97  Ordering : KBO
% 10.86/3.97  
% 10.86/3.97  Simplification rules
% 10.86/3.97  ----------------------
% 10.86/3.97  #Subsume      : 1203
% 10.86/3.97  #Demod        : 487
% 10.86/3.97  #Tautology    : 282
% 10.86/3.97  #SimpNegUnit  : 416
% 10.86/3.97  #BackRed      : 141
% 10.86/3.97  
% 10.86/3.97  #Partial instantiations: 0
% 10.86/3.97  #Strategies tried      : 1
% 10.86/3.97  
% 10.86/3.97  Timing (in seconds)
% 10.86/3.97  ----------------------
% 10.86/3.97  Preprocessing        : 0.34
% 10.86/3.97  Parsing              : 0.18
% 10.86/3.97  CNF conversion       : 0.03
% 10.86/3.98  Main loop            : 2.82
% 10.86/3.98  Inferencing          : 0.65
% 10.86/3.98  Reduction            : 0.59
% 10.86/3.98  Demodulation         : 0.38
% 10.86/3.98  BG Simplification    : 0.08
% 10.86/3.98  Subsumption          : 1.30
% 10.86/3.98  Abstraction          : 0.11
% 10.86/3.98  MUC search           : 0.00
% 10.86/3.98  Cooper               : 0.00
% 10.86/3.98  Total                : 3.19
% 10.86/3.98  Index Insertion      : 0.00
% 10.86/3.98  Index Deletion       : 0.00
% 10.86/3.98  Index Matching       : 0.00
% 10.86/3.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
