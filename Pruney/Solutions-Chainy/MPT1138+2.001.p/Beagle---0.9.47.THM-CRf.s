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
% DateTime   : Thu Dec  3 10:19:20 EST 2020

% Result     : Theorem 7.55s
% Output     : CNFRefutation 7.55s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 261 expanded)
%              Number of leaves         :   33 ( 106 expanded)
%              Depth                    :   17
%              Number of atoms          :  290 (1236 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > r8_relat_2 > r2_hidden > m1_subset_1 > v4_orders_2 > v1_xboole_0 > v1_relat_1 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(r8_relat_2,type,(
    r8_relat_2: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_120,negated_conjecture,(
    ~ ! [A] :
        ( ( v4_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( ( r1_orders_2(A,B,C)
                        & r1_orders_2(A,C,D) )
                     => r1_orders_2(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_orders_2)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

tff(f_30,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r8_relat_2(A,B)
        <=> ! [C,D,E] :
              ( ( r2_hidden(C,B)
                & r2_hidden(D,B)
                & r2_hidden(E,B)
                & r2_hidden(k4_tarski(C,D),A)
                & r2_hidden(k4_tarski(D,E),A) )
             => r2_hidden(k4_tarski(C,E),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_2)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v4_orders_2(A)
      <=> r8_relat_2(u1_orders_2(A),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_orders_2)).

tff(c_38,plain,(
    ~ r1_orders_2('#skF_5','#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_42,plain,(
    r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_50,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_44,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_119,plain,(
    ! [A_89] :
      ( m1_subset_1(u1_orders_2(A_89),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_89),u1_struct_0(A_89))))
      | ~ l1_orders_2(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_10,plain,(
    ! [C_14,A_12,B_13] :
      ( v1_relat_1(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_127,plain,(
    ! [A_89] :
      ( v1_relat_1(u1_orders_2(A_89))
      | ~ l1_orders_2(A_89) ) ),
    inference(resolution,[status(thm)],[c_119,c_10])).

tff(c_46,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_197,plain,(
    ! [B_118,C_119,A_120] :
      ( r2_hidden(k4_tarski(B_118,C_119),u1_orders_2(A_120))
      | ~ r1_orders_2(A_120,B_118,C_119)
      | ~ m1_subset_1(C_119,u1_struct_0(A_120))
      | ~ m1_subset_1(B_118,u1_struct_0(A_120))
      | ~ l1_orders_2(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_217,plain,(
    ! [A_124,B_125,C_126] :
      ( ~ v1_xboole_0(u1_orders_2(A_124))
      | ~ r1_orders_2(A_124,B_125,C_126)
      | ~ m1_subset_1(C_126,u1_struct_0(A_124))
      | ~ m1_subset_1(B_125,u1_struct_0(A_124))
      | ~ l1_orders_2(A_124) ) ),
    inference(resolution,[status(thm)],[c_197,c_2])).

tff(c_219,plain,
    ( ~ v1_xboole_0(u1_orders_2('#skF_5'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_217])).

tff(c_224,plain,(
    ~ v1_xboole_0(u1_orders_2('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_219])).

tff(c_8,plain,(
    ! [A_10,B_11] :
      ( r2_hidden(A_10,B_11)
      | v1_xboole_0(B_11)
      | ~ m1_subset_1(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20,plain,(
    ! [A_19,B_33] :
      ( r2_hidden(k4_tarski('#skF_2'(A_19,B_33),'#skF_3'(A_19,B_33)),A_19)
      | r8_relat_2(A_19,B_33)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_233,plain,(
    ! [E_143,A_144,B_142,C_145,D_146] :
      ( r2_hidden(k4_tarski(C_145,E_143),A_144)
      | ~ r2_hidden(k4_tarski(D_146,E_143),A_144)
      | ~ r2_hidden(k4_tarski(C_145,D_146),A_144)
      | ~ r2_hidden(E_143,B_142)
      | ~ r2_hidden(D_146,B_142)
      | ~ r2_hidden(C_145,B_142)
      | ~ r8_relat_2(A_144,B_142)
      | ~ v1_relat_1(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_271,plain,(
    ! [C_162,B_159,B_160,D_163,E_161] :
      ( r2_hidden(k4_tarski(C_162,E_161),B_160)
      | ~ r2_hidden(k4_tarski(C_162,D_163),B_160)
      | ~ r2_hidden(E_161,B_159)
      | ~ r2_hidden(D_163,B_159)
      | ~ r2_hidden(C_162,B_159)
      | ~ r8_relat_2(B_160,B_159)
      | ~ v1_relat_1(B_160)
      | v1_xboole_0(B_160)
      | ~ m1_subset_1(k4_tarski(D_163,E_161),B_160) ) ),
    inference(resolution,[status(thm)],[c_8,c_233])).

tff(c_482,plain,(
    ! [A_232,B_233,E_234,B_235] :
      ( r2_hidden(k4_tarski('#skF_2'(A_232,B_233),E_234),A_232)
      | ~ r2_hidden(E_234,B_235)
      | ~ r2_hidden('#skF_3'(A_232,B_233),B_235)
      | ~ r2_hidden('#skF_2'(A_232,B_233),B_235)
      | ~ r8_relat_2(A_232,B_235)
      | v1_xboole_0(A_232)
      | ~ m1_subset_1(k4_tarski('#skF_3'(A_232,B_233),E_234),A_232)
      | r8_relat_2(A_232,B_233)
      | ~ v1_relat_1(A_232) ) ),
    inference(resolution,[status(thm)],[c_20,c_271])).

tff(c_563,plain,(
    ! [A_274,B_275,A_276,B_277] :
      ( r2_hidden(k4_tarski('#skF_2'(A_274,B_275),A_276),A_274)
      | ~ r2_hidden('#skF_3'(A_274,B_275),B_277)
      | ~ r2_hidden('#skF_2'(A_274,B_275),B_277)
      | ~ r8_relat_2(A_274,B_277)
      | v1_xboole_0(A_274)
      | ~ m1_subset_1(k4_tarski('#skF_3'(A_274,B_275),A_276),A_274)
      | r8_relat_2(A_274,B_275)
      | ~ v1_relat_1(A_274)
      | v1_xboole_0(B_277)
      | ~ m1_subset_1(A_276,B_277) ) ),
    inference(resolution,[status(thm)],[c_8,c_482])).

tff(c_620,plain,(
    ! [A_294,B_295,A_296,B_297] :
      ( r2_hidden(k4_tarski('#skF_2'(A_294,B_295),A_296),A_294)
      | ~ r2_hidden('#skF_2'(A_294,B_295),B_297)
      | ~ r8_relat_2(A_294,B_297)
      | v1_xboole_0(A_294)
      | ~ m1_subset_1(k4_tarski('#skF_3'(A_294,B_295),A_296),A_294)
      | r8_relat_2(A_294,B_295)
      | ~ v1_relat_1(A_294)
      | ~ m1_subset_1(A_296,B_297)
      | v1_xboole_0(B_297)
      | ~ m1_subset_1('#skF_3'(A_294,B_295),B_297) ) ),
    inference(resolution,[status(thm)],[c_8,c_563])).

tff(c_657,plain,(
    ! [A_322,B_323,A_324,B_325] :
      ( r2_hidden(k4_tarski('#skF_2'(A_322,B_323),A_324),A_322)
      | ~ r8_relat_2(A_322,B_325)
      | v1_xboole_0(A_322)
      | ~ m1_subset_1(k4_tarski('#skF_3'(A_322,B_323),A_324),A_322)
      | r8_relat_2(A_322,B_323)
      | ~ v1_relat_1(A_322)
      | ~ m1_subset_1(A_324,B_325)
      | ~ m1_subset_1('#skF_3'(A_322,B_323),B_325)
      | v1_xboole_0(B_325)
      | ~ m1_subset_1('#skF_2'(A_322,B_323),B_325) ) ),
    inference(resolution,[status(thm)],[c_8,c_620])).

tff(c_667,plain,(
    ! [A_322,B_323] :
      ( r2_hidden(k4_tarski('#skF_2'(A_322,B_323),'#skF_6'),A_322)
      | ~ r8_relat_2(A_322,u1_struct_0('#skF_5'))
      | v1_xboole_0(A_322)
      | ~ m1_subset_1(k4_tarski('#skF_3'(A_322,B_323),'#skF_6'),A_322)
      | r8_relat_2(A_322,B_323)
      | ~ v1_relat_1(A_322)
      | ~ m1_subset_1('#skF_3'(A_322,B_323),u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_2'(A_322,B_323),u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_48,c_657])).

tff(c_686,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_667])).

tff(c_12,plain,(
    ! [C_18,B_16,A_15] :
      ( v1_xboole_0(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(B_16,A_15)))
      | ~ v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_126,plain,(
    ! [A_89] :
      ( v1_xboole_0(u1_orders_2(A_89))
      | ~ v1_xboole_0(u1_struct_0(A_89))
      | ~ l1_orders_2(A_89) ) ),
    inference(resolution,[status(thm)],[c_119,c_12])).

tff(c_714,plain,
    ( v1_xboole_0(u1_orders_2('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_686,c_126])).

tff(c_720,plain,(
    v1_xboole_0(u1_orders_2('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_714])).

tff(c_722,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_720])).

tff(c_724,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_667])).

tff(c_52,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_30,plain,(
    ! [A_43] :
      ( r8_relat_2(u1_orders_2(A_43),u1_struct_0(A_43))
      | ~ v4_orders_2(A_43)
      | ~ l1_orders_2(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_34,plain,(
    ! [B_48,C_50,A_44] :
      ( r2_hidden(k4_tarski(B_48,C_50),u1_orders_2(A_44))
      | ~ r1_orders_2(A_44,B_48,C_50)
      | ~ m1_subset_1(C_50,u1_struct_0(A_44))
      | ~ m1_subset_1(B_48,u1_struct_0(A_44))
      | ~ l1_orders_2(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_425,plain,(
    ! [C_215,A_218,B_216,B_217,C_219] :
      ( r2_hidden(k4_tarski(C_219,C_215),u1_orders_2(A_218))
      | ~ r2_hidden(k4_tarski(C_219,B_217),u1_orders_2(A_218))
      | ~ r2_hidden(C_215,B_216)
      | ~ r2_hidden(B_217,B_216)
      | ~ r2_hidden(C_219,B_216)
      | ~ r8_relat_2(u1_orders_2(A_218),B_216)
      | ~ v1_relat_1(u1_orders_2(A_218))
      | ~ r1_orders_2(A_218,B_217,C_215)
      | ~ m1_subset_1(C_215,u1_struct_0(A_218))
      | ~ m1_subset_1(B_217,u1_struct_0(A_218))
      | ~ l1_orders_2(A_218) ) ),
    inference(resolution,[status(thm)],[c_34,c_233])).

tff(c_536,plain,(
    ! [A_263,B_262,C_264,C_261,B_260] :
      ( r2_hidden(k4_tarski(B_262,C_264),u1_orders_2(A_263))
      | ~ r2_hidden(C_264,B_260)
      | ~ r2_hidden(C_261,B_260)
      | ~ r2_hidden(B_262,B_260)
      | ~ r8_relat_2(u1_orders_2(A_263),B_260)
      | ~ v1_relat_1(u1_orders_2(A_263))
      | ~ r1_orders_2(A_263,C_261,C_264)
      | ~ m1_subset_1(C_264,u1_struct_0(A_263))
      | ~ r1_orders_2(A_263,B_262,C_261)
      | ~ m1_subset_1(C_261,u1_struct_0(A_263))
      | ~ m1_subset_1(B_262,u1_struct_0(A_263))
      | ~ l1_orders_2(A_263) ) ),
    inference(resolution,[status(thm)],[c_34,c_425])).

tff(c_2123,plain,(
    ! [A_459,B_461,C_463,B_460,A_462] :
      ( r2_hidden(k4_tarski(B_460,A_462),u1_orders_2(A_459))
      | ~ r2_hidden(C_463,B_461)
      | ~ r2_hidden(B_460,B_461)
      | ~ r8_relat_2(u1_orders_2(A_459),B_461)
      | ~ v1_relat_1(u1_orders_2(A_459))
      | ~ r1_orders_2(A_459,C_463,A_462)
      | ~ m1_subset_1(A_462,u1_struct_0(A_459))
      | ~ r1_orders_2(A_459,B_460,C_463)
      | ~ m1_subset_1(C_463,u1_struct_0(A_459))
      | ~ m1_subset_1(B_460,u1_struct_0(A_459))
      | ~ l1_orders_2(A_459)
      | v1_xboole_0(B_461)
      | ~ m1_subset_1(A_462,B_461) ) ),
    inference(resolution,[status(thm)],[c_8,c_536])).

tff(c_2231,plain,(
    ! [A_472,B_468,A_471,B_470,A_469] :
      ( r2_hidden(k4_tarski(B_468,A_471),u1_orders_2(A_469))
      | ~ r2_hidden(B_468,B_470)
      | ~ r8_relat_2(u1_orders_2(A_469),B_470)
      | ~ v1_relat_1(u1_orders_2(A_469))
      | ~ r1_orders_2(A_469,A_472,A_471)
      | ~ m1_subset_1(A_471,u1_struct_0(A_469))
      | ~ r1_orders_2(A_469,B_468,A_472)
      | ~ m1_subset_1(A_472,u1_struct_0(A_469))
      | ~ m1_subset_1(B_468,u1_struct_0(A_469))
      | ~ l1_orders_2(A_469)
      | ~ m1_subset_1(A_471,B_470)
      | v1_xboole_0(B_470)
      | ~ m1_subset_1(A_472,B_470) ) ),
    inference(resolution,[status(thm)],[c_8,c_2123])).

tff(c_2322,plain,(
    ! [A_475,A_474,B_476,A_473,A_477] :
      ( r2_hidden(k4_tarski(A_477,A_473),u1_orders_2(A_475))
      | ~ r8_relat_2(u1_orders_2(A_475),B_476)
      | ~ v1_relat_1(u1_orders_2(A_475))
      | ~ r1_orders_2(A_475,A_474,A_473)
      | ~ m1_subset_1(A_473,u1_struct_0(A_475))
      | ~ r1_orders_2(A_475,A_477,A_474)
      | ~ m1_subset_1(A_474,u1_struct_0(A_475))
      | ~ m1_subset_1(A_477,u1_struct_0(A_475))
      | ~ l1_orders_2(A_475)
      | ~ m1_subset_1(A_473,B_476)
      | ~ m1_subset_1(A_474,B_476)
      | v1_xboole_0(B_476)
      | ~ m1_subset_1(A_477,B_476) ) ),
    inference(resolution,[status(thm)],[c_8,c_2231])).

tff(c_2334,plain,(
    ! [A_478,A_479,A_480,A_481] :
      ( r2_hidden(k4_tarski(A_478,A_479),u1_orders_2(A_480))
      | ~ v1_relat_1(u1_orders_2(A_480))
      | ~ r1_orders_2(A_480,A_481,A_479)
      | ~ r1_orders_2(A_480,A_478,A_481)
      | ~ m1_subset_1(A_479,u1_struct_0(A_480))
      | ~ m1_subset_1(A_481,u1_struct_0(A_480))
      | v1_xboole_0(u1_struct_0(A_480))
      | ~ m1_subset_1(A_478,u1_struct_0(A_480))
      | ~ v4_orders_2(A_480)
      | ~ l1_orders_2(A_480) ) ),
    inference(resolution,[status(thm)],[c_30,c_2322])).

tff(c_2340,plain,(
    ! [A_478] :
      ( r2_hidden(k4_tarski(A_478,'#skF_7'),u1_orders_2('#skF_5'))
      | ~ v1_relat_1(u1_orders_2('#skF_5'))
      | ~ r1_orders_2('#skF_5',A_478,'#skF_6')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_478,u1_struct_0('#skF_5'))
      | ~ v4_orders_2('#skF_5')
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_42,c_2334])).

tff(c_2347,plain,(
    ! [A_478] :
      ( r2_hidden(k4_tarski(A_478,'#skF_7'),u1_orders_2('#skF_5'))
      | ~ v1_relat_1(u1_orders_2('#skF_5'))
      | ~ r1_orders_2('#skF_5',A_478,'#skF_6')
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_478,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_48,c_46,c_2340])).

tff(c_2348,plain,(
    ! [A_478] :
      ( r2_hidden(k4_tarski(A_478,'#skF_7'),u1_orders_2('#skF_5'))
      | ~ v1_relat_1(u1_orders_2('#skF_5'))
      | ~ r1_orders_2('#skF_5',A_478,'#skF_6')
      | ~ m1_subset_1(A_478,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_724,c_2347])).

tff(c_2353,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_2348])).

tff(c_2356,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_127,c_2353])).

tff(c_2360,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2356])).

tff(c_2362,plain,(
    v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_2348])).

tff(c_40,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_2342,plain,(
    ! [A_478] :
      ( r2_hidden(k4_tarski(A_478,'#skF_8'),u1_orders_2('#skF_5'))
      | ~ v1_relat_1(u1_orders_2('#skF_5'))
      | ~ r1_orders_2('#skF_5',A_478,'#skF_7')
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_478,u1_struct_0('#skF_5'))
      | ~ v4_orders_2('#skF_5')
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_2334])).

tff(c_2351,plain,(
    ! [A_478] :
      ( r2_hidden(k4_tarski(A_478,'#skF_8'),u1_orders_2('#skF_5'))
      | ~ v1_relat_1(u1_orders_2('#skF_5'))
      | ~ r1_orders_2('#skF_5',A_478,'#skF_7')
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_478,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_46,c_44,c_2342])).

tff(c_2352,plain,(
    ! [A_478] :
      ( r2_hidden(k4_tarski(A_478,'#skF_8'),u1_orders_2('#skF_5'))
      | ~ v1_relat_1(u1_orders_2('#skF_5'))
      | ~ r1_orders_2('#skF_5',A_478,'#skF_7')
      | ~ m1_subset_1(A_478,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_724,c_2351])).

tff(c_2553,plain,(
    ! [A_488] :
      ( r2_hidden(k4_tarski(A_488,'#skF_8'),u1_orders_2('#skF_5'))
      | ~ r1_orders_2('#skF_5',A_488,'#skF_7')
      | ~ m1_subset_1(A_488,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2362,c_2352])).

tff(c_32,plain,(
    ! [A_44,B_48,C_50] :
      ( r1_orders_2(A_44,B_48,C_50)
      | ~ r2_hidden(k4_tarski(B_48,C_50),u1_orders_2(A_44))
      | ~ m1_subset_1(C_50,u1_struct_0(A_44))
      | ~ m1_subset_1(B_48,u1_struct_0(A_44))
      | ~ l1_orders_2(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2590,plain,(
    ! [A_488] :
      ( r1_orders_2('#skF_5',A_488,'#skF_8')
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ r1_orders_2('#skF_5',A_488,'#skF_7')
      | ~ m1_subset_1(A_488,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_2553,c_32])).

tff(c_2634,plain,(
    ! [A_489] :
      ( r1_orders_2('#skF_5',A_489,'#skF_8')
      | ~ r1_orders_2('#skF_5',A_489,'#skF_7')
      | ~ m1_subset_1(A_489,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44,c_2590])).

tff(c_2637,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_8')
    | ~ r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_48,c_2634])).

tff(c_2646,plain,(
    r1_orders_2('#skF_5','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2637])).

tff(c_2648,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_2646])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 18:30:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.55/2.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.55/2.93  
% 7.55/2.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.55/2.93  %$ r1_orders_2 > r8_relat_2 > r2_hidden > m1_subset_1 > v4_orders_2 > v1_xboole_0 > v1_relat_1 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 7.55/2.93  
% 7.55/2.93  %Foreground sorts:
% 7.55/2.93  
% 7.55/2.93  
% 7.55/2.93  %Background operators:
% 7.55/2.93  
% 7.55/2.93  
% 7.55/2.93  %Foreground operators:
% 7.55/2.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.55/2.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.55/2.93  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.55/2.93  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 7.55/2.93  tff('#skF_7', type, '#skF_7': $i).
% 7.55/2.93  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.55/2.93  tff('#skF_5', type, '#skF_5': $i).
% 7.55/2.93  tff('#skF_6', type, '#skF_6': $i).
% 7.55/2.93  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 7.55/2.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.55/2.93  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 7.55/2.93  tff('#skF_8', type, '#skF_8': $i).
% 7.55/2.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.55/2.93  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.55/2.93  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.55/2.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.55/2.93  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.55/2.93  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 7.55/2.93  tff(r8_relat_2, type, r8_relat_2: ($i * $i) > $o).
% 7.55/2.93  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.55/2.93  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.55/2.93  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.55/2.93  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.55/2.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.55/2.93  
% 7.55/2.95  tff(f_120, negated_conjecture, ~(![A]: ((v4_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r1_orders_2(A, B, C) & r1_orders_2(A, C, D)) => r1_orders_2(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_orders_2)).
% 7.55/2.95  tff(f_100, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 7.55/2.95  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.55/2.95  tff(f_96, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_orders_2(A, B, C) <=> r2_hidden(k4_tarski(B, C), u1_orders_2(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_orders_2)).
% 7.55/2.95  tff(f_30, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_boole)).
% 7.55/2.95  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 7.55/2.95  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (![B]: (r8_relat_2(A, B) <=> (![C, D, E]: (((((r2_hidden(C, B) & r2_hidden(D, B)) & r2_hidden(E, B)) & r2_hidden(k4_tarski(C, D), A)) & r2_hidden(k4_tarski(D, E), A)) => r2_hidden(k4_tarski(C, E), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_relat_2)).
% 7.55/2.95  tff(f_60, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 7.55/2.95  tff(f_84, axiom, (![A]: (l1_orders_2(A) => (v4_orders_2(A) <=> r8_relat_2(u1_orders_2(A), u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_orders_2)).
% 7.55/2.95  tff(c_38, plain, (~r1_orders_2('#skF_5', '#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.55/2.95  tff(c_42, plain, (r1_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.55/2.95  tff(c_48, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.55/2.95  tff(c_50, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.55/2.95  tff(c_44, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.55/2.95  tff(c_119, plain, (![A_89]: (m1_subset_1(u1_orders_2(A_89), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_89), u1_struct_0(A_89)))) | ~l1_orders_2(A_89))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.55/2.95  tff(c_10, plain, (![C_14, A_12, B_13]: (v1_relat_1(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.55/2.95  tff(c_127, plain, (![A_89]: (v1_relat_1(u1_orders_2(A_89)) | ~l1_orders_2(A_89))), inference(resolution, [status(thm)], [c_119, c_10])).
% 7.55/2.95  tff(c_46, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.55/2.95  tff(c_197, plain, (![B_118, C_119, A_120]: (r2_hidden(k4_tarski(B_118, C_119), u1_orders_2(A_120)) | ~r1_orders_2(A_120, B_118, C_119) | ~m1_subset_1(C_119, u1_struct_0(A_120)) | ~m1_subset_1(B_118, u1_struct_0(A_120)) | ~l1_orders_2(A_120))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.55/2.95  tff(c_2, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 7.55/2.95  tff(c_217, plain, (![A_124, B_125, C_126]: (~v1_xboole_0(u1_orders_2(A_124)) | ~r1_orders_2(A_124, B_125, C_126) | ~m1_subset_1(C_126, u1_struct_0(A_124)) | ~m1_subset_1(B_125, u1_struct_0(A_124)) | ~l1_orders_2(A_124))), inference(resolution, [status(thm)], [c_197, c_2])).
% 7.55/2.95  tff(c_219, plain, (~v1_xboole_0(u1_orders_2('#skF_5')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_42, c_217])).
% 7.55/2.95  tff(c_224, plain, (~v1_xboole_0(u1_orders_2('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_219])).
% 7.55/2.95  tff(c_8, plain, (![A_10, B_11]: (r2_hidden(A_10, B_11) | v1_xboole_0(B_11) | ~m1_subset_1(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.55/2.95  tff(c_20, plain, (![A_19, B_33]: (r2_hidden(k4_tarski('#skF_2'(A_19, B_33), '#skF_3'(A_19, B_33)), A_19) | r8_relat_2(A_19, B_33) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.55/2.95  tff(c_233, plain, (![E_143, A_144, B_142, C_145, D_146]: (r2_hidden(k4_tarski(C_145, E_143), A_144) | ~r2_hidden(k4_tarski(D_146, E_143), A_144) | ~r2_hidden(k4_tarski(C_145, D_146), A_144) | ~r2_hidden(E_143, B_142) | ~r2_hidden(D_146, B_142) | ~r2_hidden(C_145, B_142) | ~r8_relat_2(A_144, B_142) | ~v1_relat_1(A_144))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.55/2.95  tff(c_271, plain, (![C_162, B_159, B_160, D_163, E_161]: (r2_hidden(k4_tarski(C_162, E_161), B_160) | ~r2_hidden(k4_tarski(C_162, D_163), B_160) | ~r2_hidden(E_161, B_159) | ~r2_hidden(D_163, B_159) | ~r2_hidden(C_162, B_159) | ~r8_relat_2(B_160, B_159) | ~v1_relat_1(B_160) | v1_xboole_0(B_160) | ~m1_subset_1(k4_tarski(D_163, E_161), B_160))), inference(resolution, [status(thm)], [c_8, c_233])).
% 7.55/2.95  tff(c_482, plain, (![A_232, B_233, E_234, B_235]: (r2_hidden(k4_tarski('#skF_2'(A_232, B_233), E_234), A_232) | ~r2_hidden(E_234, B_235) | ~r2_hidden('#skF_3'(A_232, B_233), B_235) | ~r2_hidden('#skF_2'(A_232, B_233), B_235) | ~r8_relat_2(A_232, B_235) | v1_xboole_0(A_232) | ~m1_subset_1(k4_tarski('#skF_3'(A_232, B_233), E_234), A_232) | r8_relat_2(A_232, B_233) | ~v1_relat_1(A_232))), inference(resolution, [status(thm)], [c_20, c_271])).
% 7.55/2.95  tff(c_563, plain, (![A_274, B_275, A_276, B_277]: (r2_hidden(k4_tarski('#skF_2'(A_274, B_275), A_276), A_274) | ~r2_hidden('#skF_3'(A_274, B_275), B_277) | ~r2_hidden('#skF_2'(A_274, B_275), B_277) | ~r8_relat_2(A_274, B_277) | v1_xboole_0(A_274) | ~m1_subset_1(k4_tarski('#skF_3'(A_274, B_275), A_276), A_274) | r8_relat_2(A_274, B_275) | ~v1_relat_1(A_274) | v1_xboole_0(B_277) | ~m1_subset_1(A_276, B_277))), inference(resolution, [status(thm)], [c_8, c_482])).
% 7.55/2.95  tff(c_620, plain, (![A_294, B_295, A_296, B_297]: (r2_hidden(k4_tarski('#skF_2'(A_294, B_295), A_296), A_294) | ~r2_hidden('#skF_2'(A_294, B_295), B_297) | ~r8_relat_2(A_294, B_297) | v1_xboole_0(A_294) | ~m1_subset_1(k4_tarski('#skF_3'(A_294, B_295), A_296), A_294) | r8_relat_2(A_294, B_295) | ~v1_relat_1(A_294) | ~m1_subset_1(A_296, B_297) | v1_xboole_0(B_297) | ~m1_subset_1('#skF_3'(A_294, B_295), B_297))), inference(resolution, [status(thm)], [c_8, c_563])).
% 7.55/2.95  tff(c_657, plain, (![A_322, B_323, A_324, B_325]: (r2_hidden(k4_tarski('#skF_2'(A_322, B_323), A_324), A_322) | ~r8_relat_2(A_322, B_325) | v1_xboole_0(A_322) | ~m1_subset_1(k4_tarski('#skF_3'(A_322, B_323), A_324), A_322) | r8_relat_2(A_322, B_323) | ~v1_relat_1(A_322) | ~m1_subset_1(A_324, B_325) | ~m1_subset_1('#skF_3'(A_322, B_323), B_325) | v1_xboole_0(B_325) | ~m1_subset_1('#skF_2'(A_322, B_323), B_325))), inference(resolution, [status(thm)], [c_8, c_620])).
% 7.55/2.95  tff(c_667, plain, (![A_322, B_323]: (r2_hidden(k4_tarski('#skF_2'(A_322, B_323), '#skF_6'), A_322) | ~r8_relat_2(A_322, u1_struct_0('#skF_5')) | v1_xboole_0(A_322) | ~m1_subset_1(k4_tarski('#skF_3'(A_322, B_323), '#skF_6'), A_322) | r8_relat_2(A_322, B_323) | ~v1_relat_1(A_322) | ~m1_subset_1('#skF_3'(A_322, B_323), u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_2'(A_322, B_323), u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_48, c_657])).
% 7.55/2.95  tff(c_686, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_667])).
% 7.55/2.95  tff(c_12, plain, (![C_18, B_16, A_15]: (v1_xboole_0(C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(B_16, A_15))) | ~v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.55/2.95  tff(c_126, plain, (![A_89]: (v1_xboole_0(u1_orders_2(A_89)) | ~v1_xboole_0(u1_struct_0(A_89)) | ~l1_orders_2(A_89))), inference(resolution, [status(thm)], [c_119, c_12])).
% 7.55/2.95  tff(c_714, plain, (v1_xboole_0(u1_orders_2('#skF_5')) | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_686, c_126])).
% 7.55/2.95  tff(c_720, plain, (v1_xboole_0(u1_orders_2('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_714])).
% 7.55/2.95  tff(c_722, plain, $false, inference(negUnitSimplification, [status(thm)], [c_224, c_720])).
% 7.55/2.95  tff(c_724, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_667])).
% 7.55/2.95  tff(c_52, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.55/2.95  tff(c_30, plain, (![A_43]: (r8_relat_2(u1_orders_2(A_43), u1_struct_0(A_43)) | ~v4_orders_2(A_43) | ~l1_orders_2(A_43))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.55/2.95  tff(c_34, plain, (![B_48, C_50, A_44]: (r2_hidden(k4_tarski(B_48, C_50), u1_orders_2(A_44)) | ~r1_orders_2(A_44, B_48, C_50) | ~m1_subset_1(C_50, u1_struct_0(A_44)) | ~m1_subset_1(B_48, u1_struct_0(A_44)) | ~l1_orders_2(A_44))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.55/2.95  tff(c_425, plain, (![C_215, A_218, B_216, B_217, C_219]: (r2_hidden(k4_tarski(C_219, C_215), u1_orders_2(A_218)) | ~r2_hidden(k4_tarski(C_219, B_217), u1_orders_2(A_218)) | ~r2_hidden(C_215, B_216) | ~r2_hidden(B_217, B_216) | ~r2_hidden(C_219, B_216) | ~r8_relat_2(u1_orders_2(A_218), B_216) | ~v1_relat_1(u1_orders_2(A_218)) | ~r1_orders_2(A_218, B_217, C_215) | ~m1_subset_1(C_215, u1_struct_0(A_218)) | ~m1_subset_1(B_217, u1_struct_0(A_218)) | ~l1_orders_2(A_218))), inference(resolution, [status(thm)], [c_34, c_233])).
% 7.55/2.95  tff(c_536, plain, (![A_263, B_262, C_264, C_261, B_260]: (r2_hidden(k4_tarski(B_262, C_264), u1_orders_2(A_263)) | ~r2_hidden(C_264, B_260) | ~r2_hidden(C_261, B_260) | ~r2_hidden(B_262, B_260) | ~r8_relat_2(u1_orders_2(A_263), B_260) | ~v1_relat_1(u1_orders_2(A_263)) | ~r1_orders_2(A_263, C_261, C_264) | ~m1_subset_1(C_264, u1_struct_0(A_263)) | ~r1_orders_2(A_263, B_262, C_261) | ~m1_subset_1(C_261, u1_struct_0(A_263)) | ~m1_subset_1(B_262, u1_struct_0(A_263)) | ~l1_orders_2(A_263))), inference(resolution, [status(thm)], [c_34, c_425])).
% 7.55/2.95  tff(c_2123, plain, (![A_459, B_461, C_463, B_460, A_462]: (r2_hidden(k4_tarski(B_460, A_462), u1_orders_2(A_459)) | ~r2_hidden(C_463, B_461) | ~r2_hidden(B_460, B_461) | ~r8_relat_2(u1_orders_2(A_459), B_461) | ~v1_relat_1(u1_orders_2(A_459)) | ~r1_orders_2(A_459, C_463, A_462) | ~m1_subset_1(A_462, u1_struct_0(A_459)) | ~r1_orders_2(A_459, B_460, C_463) | ~m1_subset_1(C_463, u1_struct_0(A_459)) | ~m1_subset_1(B_460, u1_struct_0(A_459)) | ~l1_orders_2(A_459) | v1_xboole_0(B_461) | ~m1_subset_1(A_462, B_461))), inference(resolution, [status(thm)], [c_8, c_536])).
% 7.55/2.95  tff(c_2231, plain, (![A_472, B_468, A_471, B_470, A_469]: (r2_hidden(k4_tarski(B_468, A_471), u1_orders_2(A_469)) | ~r2_hidden(B_468, B_470) | ~r8_relat_2(u1_orders_2(A_469), B_470) | ~v1_relat_1(u1_orders_2(A_469)) | ~r1_orders_2(A_469, A_472, A_471) | ~m1_subset_1(A_471, u1_struct_0(A_469)) | ~r1_orders_2(A_469, B_468, A_472) | ~m1_subset_1(A_472, u1_struct_0(A_469)) | ~m1_subset_1(B_468, u1_struct_0(A_469)) | ~l1_orders_2(A_469) | ~m1_subset_1(A_471, B_470) | v1_xboole_0(B_470) | ~m1_subset_1(A_472, B_470))), inference(resolution, [status(thm)], [c_8, c_2123])).
% 7.55/2.95  tff(c_2322, plain, (![A_475, A_474, B_476, A_473, A_477]: (r2_hidden(k4_tarski(A_477, A_473), u1_orders_2(A_475)) | ~r8_relat_2(u1_orders_2(A_475), B_476) | ~v1_relat_1(u1_orders_2(A_475)) | ~r1_orders_2(A_475, A_474, A_473) | ~m1_subset_1(A_473, u1_struct_0(A_475)) | ~r1_orders_2(A_475, A_477, A_474) | ~m1_subset_1(A_474, u1_struct_0(A_475)) | ~m1_subset_1(A_477, u1_struct_0(A_475)) | ~l1_orders_2(A_475) | ~m1_subset_1(A_473, B_476) | ~m1_subset_1(A_474, B_476) | v1_xboole_0(B_476) | ~m1_subset_1(A_477, B_476))), inference(resolution, [status(thm)], [c_8, c_2231])).
% 7.55/2.95  tff(c_2334, plain, (![A_478, A_479, A_480, A_481]: (r2_hidden(k4_tarski(A_478, A_479), u1_orders_2(A_480)) | ~v1_relat_1(u1_orders_2(A_480)) | ~r1_orders_2(A_480, A_481, A_479) | ~r1_orders_2(A_480, A_478, A_481) | ~m1_subset_1(A_479, u1_struct_0(A_480)) | ~m1_subset_1(A_481, u1_struct_0(A_480)) | v1_xboole_0(u1_struct_0(A_480)) | ~m1_subset_1(A_478, u1_struct_0(A_480)) | ~v4_orders_2(A_480) | ~l1_orders_2(A_480))), inference(resolution, [status(thm)], [c_30, c_2322])).
% 7.55/2.95  tff(c_2340, plain, (![A_478]: (r2_hidden(k4_tarski(A_478, '#skF_7'), u1_orders_2('#skF_5')) | ~v1_relat_1(u1_orders_2('#skF_5')) | ~r1_orders_2('#skF_5', A_478, '#skF_6') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1(A_478, u1_struct_0('#skF_5')) | ~v4_orders_2('#skF_5') | ~l1_orders_2('#skF_5'))), inference(resolution, [status(thm)], [c_42, c_2334])).
% 7.55/2.95  tff(c_2347, plain, (![A_478]: (r2_hidden(k4_tarski(A_478, '#skF_7'), u1_orders_2('#skF_5')) | ~v1_relat_1(u1_orders_2('#skF_5')) | ~r1_orders_2('#skF_5', A_478, '#skF_6') | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1(A_478, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52, c_48, c_46, c_2340])).
% 7.55/2.95  tff(c_2348, plain, (![A_478]: (r2_hidden(k4_tarski(A_478, '#skF_7'), u1_orders_2('#skF_5')) | ~v1_relat_1(u1_orders_2('#skF_5')) | ~r1_orders_2('#skF_5', A_478, '#skF_6') | ~m1_subset_1(A_478, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_724, c_2347])).
% 7.55/2.95  tff(c_2353, plain, (~v1_relat_1(u1_orders_2('#skF_5'))), inference(splitLeft, [status(thm)], [c_2348])).
% 7.55/2.95  tff(c_2356, plain, (~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_127, c_2353])).
% 7.55/2.95  tff(c_2360, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_2356])).
% 7.55/2.95  tff(c_2362, plain, (v1_relat_1(u1_orders_2('#skF_5'))), inference(splitRight, [status(thm)], [c_2348])).
% 7.55/2.95  tff(c_40, plain, (r1_orders_2('#skF_5', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.55/2.95  tff(c_2342, plain, (![A_478]: (r2_hidden(k4_tarski(A_478, '#skF_8'), u1_orders_2('#skF_5')) | ~v1_relat_1(u1_orders_2('#skF_5')) | ~r1_orders_2('#skF_5', A_478, '#skF_7') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1(A_478, u1_struct_0('#skF_5')) | ~v4_orders_2('#skF_5') | ~l1_orders_2('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_2334])).
% 7.55/2.95  tff(c_2351, plain, (![A_478]: (r2_hidden(k4_tarski(A_478, '#skF_8'), u1_orders_2('#skF_5')) | ~v1_relat_1(u1_orders_2('#skF_5')) | ~r1_orders_2('#skF_5', A_478, '#skF_7') | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1(A_478, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52, c_46, c_44, c_2342])).
% 7.55/2.95  tff(c_2352, plain, (![A_478]: (r2_hidden(k4_tarski(A_478, '#skF_8'), u1_orders_2('#skF_5')) | ~v1_relat_1(u1_orders_2('#skF_5')) | ~r1_orders_2('#skF_5', A_478, '#skF_7') | ~m1_subset_1(A_478, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_724, c_2351])).
% 7.55/2.95  tff(c_2553, plain, (![A_488]: (r2_hidden(k4_tarski(A_488, '#skF_8'), u1_orders_2('#skF_5')) | ~r1_orders_2('#skF_5', A_488, '#skF_7') | ~m1_subset_1(A_488, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_2362, c_2352])).
% 7.55/2.95  tff(c_32, plain, (![A_44, B_48, C_50]: (r1_orders_2(A_44, B_48, C_50) | ~r2_hidden(k4_tarski(B_48, C_50), u1_orders_2(A_44)) | ~m1_subset_1(C_50, u1_struct_0(A_44)) | ~m1_subset_1(B_48, u1_struct_0(A_44)) | ~l1_orders_2(A_44))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.55/2.95  tff(c_2590, plain, (![A_488]: (r1_orders_2('#skF_5', A_488, '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~r1_orders_2('#skF_5', A_488, '#skF_7') | ~m1_subset_1(A_488, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_2553, c_32])).
% 7.55/2.95  tff(c_2634, plain, (![A_489]: (r1_orders_2('#skF_5', A_489, '#skF_8') | ~r1_orders_2('#skF_5', A_489, '#skF_7') | ~m1_subset_1(A_489, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_44, c_2590])).
% 7.55/2.95  tff(c_2637, plain, (r1_orders_2('#skF_5', '#skF_6', '#skF_8') | ~r1_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_48, c_2634])).
% 7.55/2.95  tff(c_2646, plain, (r1_orders_2('#skF_5', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2637])).
% 7.55/2.95  tff(c_2648, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_2646])).
% 7.55/2.95  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.55/2.95  
% 7.55/2.95  Inference rules
% 7.55/2.95  ----------------------
% 7.55/2.95  #Ref     : 0
% 7.55/2.95  #Sup     : 721
% 7.55/2.95  #Fact    : 0
% 7.55/2.95  #Define  : 0
% 7.55/2.95  #Split   : 4
% 7.55/2.95  #Chain   : 0
% 7.55/2.95  #Close   : 0
% 7.55/2.95  
% 7.55/2.95  Ordering : KBO
% 7.55/2.95  
% 7.55/2.95  Simplification rules
% 7.55/2.95  ----------------------
% 7.55/2.95  #Subsume      : 32
% 7.55/2.95  #Demod        : 33
% 7.55/2.95  #Tautology    : 26
% 7.55/2.95  #SimpNegUnit  : 23
% 7.55/2.95  #BackRed      : 0
% 7.55/2.95  
% 7.55/2.95  #Partial instantiations: 0
% 7.55/2.95  #Strategies tried      : 1
% 7.55/2.95  
% 7.55/2.95  Timing (in seconds)
% 7.55/2.95  ----------------------
% 7.55/2.95  Preprocessing        : 0.33
% 7.55/2.95  Parsing              : 0.19
% 7.55/2.95  CNF conversion       : 0.03
% 7.55/2.95  Main loop            : 1.77
% 7.55/2.95  Inferencing          : 0.35
% 7.55/2.95  Reduction            : 0.26
% 7.55/2.95  Demodulation         : 0.17
% 7.55/2.95  BG Simplification    : 0.04
% 7.55/2.95  Subsumption          : 1.03
% 7.55/2.95  Abstraction          : 0.06
% 7.55/2.95  MUC search           : 0.00
% 7.55/2.95  Cooper               : 0.00
% 7.55/2.95  Total                : 2.14
% 7.55/2.95  Index Insertion      : 0.00
% 7.55/2.95  Index Deletion       : 0.00
% 7.55/2.95  Index Matching       : 0.00
% 7.55/2.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
