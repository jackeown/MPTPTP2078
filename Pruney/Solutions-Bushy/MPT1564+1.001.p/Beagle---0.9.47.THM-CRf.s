%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1564+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:04 EST 2020

% Result     : Theorem 4.72s
% Output     : CNFRefutation 4.72s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 120 expanded)
%              Number of leaves         :   34 (  58 expanded)
%              Depth                    :   14
%              Number of atoms          :  245 ( 411 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_yellow_0 > r2_hidden > r1_yellow_0 > m1_subset_1 > v5_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(v1_yellow_0,type,(
    v1_yellow_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v5_orders_2(A)
          & v1_yellow_0(A)
          & l1_orders_2(A) )
       => ( r1_yellow_0(A,k1_xboole_0)
          & r2_yellow_0(A,u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_0)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_33,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_yellow_0(A)
      <=> ? [B] :
            ( m1_subset_1(B,u1_struct_0(A))
            & r1_lattice3(A,u1_struct_0(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_yellow_0)).

tff(f_97,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( r2_yellow_0(A,B)
        <=> ? [C] :
              ( m1_subset_1(C,u1_struct_0(A))
              & r1_lattice3(A,B,C)
              & ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r1_lattice3(A,B,D)
                   => r1_orders_2(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_yellow_0)).

tff(f_103,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r1_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).

tff(f_112,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( r2_lattice3(A,k1_xboole_0,B)
            & r1_lattice3(A,k1_xboole_0,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( r1_yellow_0(A,B)
        <=> ? [C] :
              ( m1_subset_1(C,u1_struct_0(A))
              & r2_lattice3(A,B,C)
              & ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r2_lattice3(A,B,D)
                   => r1_orders_2(A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow_0)).

tff(f_59,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_52,plain,(
    l1_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_16,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_orders_2(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_54,plain,(
    v1_yellow_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_56,plain,(
    v5_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_6,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),u1_struct_0(A_1))
      | ~ v1_yellow_0(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_1] :
      ( r1_lattice3(A_1,u1_struct_0(A_1),'#skF_1'(A_1))
      | ~ v1_yellow_0(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_42,plain,(
    ! [A_44,B_58,C_65] :
      ( m1_subset_1('#skF_5'(A_44,B_58,C_65),u1_struct_0(A_44))
      | r2_yellow_0(A_44,B_58)
      | ~ r1_lattice3(A_44,B_58,C_65)
      | ~ m1_subset_1(C_65,u1_struct_0(A_44))
      | ~ l1_orders_2(A_44)
      | ~ v5_orders_2(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_40,plain,(
    ! [A_44,B_58,C_65] :
      ( r1_lattice3(A_44,B_58,'#skF_5'(A_44,B_58,C_65))
      | r2_yellow_0(A_44,B_58)
      | ~ r1_lattice3(A_44,B_58,C_65)
      | ~ m1_subset_1(C_65,u1_struct_0(A_44))
      | ~ l1_orders_2(A_44)
      | ~ v5_orders_2(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_44,plain,(
    ! [A_69,B_70] :
      ( r2_hidden(A_69,B_70)
      | v1_xboole_0(B_70)
      | ~ m1_subset_1(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_820,plain,(
    ! [A_377,C_378,D_379,B_380] :
      ( r1_orders_2(A_377,C_378,D_379)
      | ~ r2_hidden(D_379,B_380)
      | ~ m1_subset_1(D_379,u1_struct_0(A_377))
      | ~ r1_lattice3(A_377,B_380,C_378)
      | ~ m1_subset_1(C_378,u1_struct_0(A_377))
      | ~ l1_orders_2(A_377) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_875,plain,(
    ! [A_417,C_418,A_419,B_420] :
      ( r1_orders_2(A_417,C_418,A_419)
      | ~ m1_subset_1(A_419,u1_struct_0(A_417))
      | ~ r1_lattice3(A_417,B_420,C_418)
      | ~ m1_subset_1(C_418,u1_struct_0(A_417))
      | ~ l1_orders_2(A_417)
      | v1_xboole_0(B_420)
      | ~ m1_subset_1(A_419,B_420) ) ),
    inference(resolution,[status(thm)],[c_44,c_820])).

tff(c_894,plain,(
    ! [A_421,C_422,B_423] :
      ( r1_orders_2(A_421,C_422,'#skF_1'(A_421))
      | ~ r1_lattice3(A_421,B_423,C_422)
      | ~ m1_subset_1(C_422,u1_struct_0(A_421))
      | v1_xboole_0(B_423)
      | ~ m1_subset_1('#skF_1'(A_421),B_423)
      | ~ v1_yellow_0(A_421)
      | ~ l1_orders_2(A_421) ) ),
    inference(resolution,[status(thm)],[c_6,c_875])).

tff(c_1350,plain,(
    ! [A_557,B_558,C_559] :
      ( r1_orders_2(A_557,'#skF_5'(A_557,B_558,C_559),'#skF_1'(A_557))
      | ~ m1_subset_1('#skF_5'(A_557,B_558,C_559),u1_struct_0(A_557))
      | v1_xboole_0(B_558)
      | ~ m1_subset_1('#skF_1'(A_557),B_558)
      | ~ v1_yellow_0(A_557)
      | r2_yellow_0(A_557,B_558)
      | ~ r1_lattice3(A_557,B_558,C_559)
      | ~ m1_subset_1(C_559,u1_struct_0(A_557))
      | ~ l1_orders_2(A_557)
      | ~ v5_orders_2(A_557) ) ),
    inference(resolution,[status(thm)],[c_40,c_894])).

tff(c_38,plain,(
    ! [A_44,B_58,C_65] :
      ( ~ r1_orders_2(A_44,'#skF_5'(A_44,B_58,C_65),C_65)
      | r2_yellow_0(A_44,B_58)
      | ~ r1_lattice3(A_44,B_58,C_65)
      | ~ m1_subset_1(C_65,u1_struct_0(A_44))
      | ~ l1_orders_2(A_44)
      | ~ v5_orders_2(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1356,plain,(
    ! [A_560,B_561] :
      ( ~ m1_subset_1('#skF_5'(A_560,B_561,'#skF_1'(A_560)),u1_struct_0(A_560))
      | v1_xboole_0(B_561)
      | ~ m1_subset_1('#skF_1'(A_560),B_561)
      | ~ v1_yellow_0(A_560)
      | r2_yellow_0(A_560,B_561)
      | ~ r1_lattice3(A_560,B_561,'#skF_1'(A_560))
      | ~ m1_subset_1('#skF_1'(A_560),u1_struct_0(A_560))
      | ~ l1_orders_2(A_560)
      | ~ v5_orders_2(A_560) ) ),
    inference(resolution,[status(thm)],[c_1350,c_38])).

tff(c_1362,plain,(
    ! [B_562,A_563] :
      ( v1_xboole_0(B_562)
      | ~ m1_subset_1('#skF_1'(A_563),B_562)
      | ~ v1_yellow_0(A_563)
      | r2_yellow_0(A_563,B_562)
      | ~ r1_lattice3(A_563,B_562,'#skF_1'(A_563))
      | ~ m1_subset_1('#skF_1'(A_563),u1_struct_0(A_563))
      | ~ l1_orders_2(A_563)
      | ~ v5_orders_2(A_563) ) ),
    inference(resolution,[status(thm)],[c_42,c_1356])).

tff(c_1373,plain,(
    ! [A_564] :
      ( v1_xboole_0(u1_struct_0(A_564))
      | r2_yellow_0(A_564,u1_struct_0(A_564))
      | ~ m1_subset_1('#skF_1'(A_564),u1_struct_0(A_564))
      | ~ v5_orders_2(A_564)
      | ~ v1_yellow_0(A_564)
      | ~ l1_orders_2(A_564) ) ),
    inference(resolution,[status(thm)],[c_4,c_1362])).

tff(c_1378,plain,(
    ! [A_565] :
      ( v1_xboole_0(u1_struct_0(A_565))
      | r2_yellow_0(A_565,u1_struct_0(A_565))
      | ~ v5_orders_2(A_565)
      | ~ v1_yellow_0(A_565)
      | ~ l1_orders_2(A_565) ) ),
    inference(resolution,[status(thm)],[c_6,c_1373])).

tff(c_70,plain,(
    ! [A_82,B_83] :
      ( r2_lattice3(A_82,k1_xboole_0,B_83)
      | ~ m1_subset_1(B_83,u1_struct_0(A_82))
      | ~ l1_orders_2(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_74,plain,(
    ! [A_1] :
      ( r2_lattice3(A_1,k1_xboole_0,'#skF_1'(A_1))
      | ~ v1_yellow_0(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(resolution,[status(thm)],[c_6,c_70])).

tff(c_30,plain,(
    ! [A_19,B_33,C_40] :
      ( m1_subset_1('#skF_3'(A_19,B_33,C_40),u1_struct_0(A_19))
      | r1_yellow_0(A_19,B_33)
      | ~ r2_lattice3(A_19,B_33,C_40)
      | ~ m1_subset_1(C_40,u1_struct_0(A_19))
      | ~ l1_orders_2(A_19)
      | ~ v5_orders_2(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_129,plain,(
    ! [A_115,C_116,D_117,B_118] :
      ( r1_orders_2(A_115,C_116,D_117)
      | ~ r2_hidden(D_117,B_118)
      | ~ m1_subset_1(D_117,u1_struct_0(A_115))
      | ~ r1_lattice3(A_115,B_118,C_116)
      | ~ m1_subset_1(C_116,u1_struct_0(A_115))
      | ~ l1_orders_2(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_186,plain,(
    ! [A_161,C_162,A_163,B_164] :
      ( r1_orders_2(A_161,C_162,A_163)
      | ~ m1_subset_1(A_163,u1_struct_0(A_161))
      | ~ r1_lattice3(A_161,B_164,C_162)
      | ~ m1_subset_1(C_162,u1_struct_0(A_161))
      | ~ l1_orders_2(A_161)
      | v1_xboole_0(B_164)
      | ~ m1_subset_1(A_163,B_164) ) ),
    inference(resolution,[status(thm)],[c_44,c_129])).

tff(c_548,plain,(
    ! [A_268,C_266,B_267,C_269,B_265] :
      ( r1_orders_2(A_268,C_266,'#skF_3'(A_268,B_265,C_269))
      | ~ r1_lattice3(A_268,B_267,C_266)
      | ~ m1_subset_1(C_266,u1_struct_0(A_268))
      | v1_xboole_0(B_267)
      | ~ m1_subset_1('#skF_3'(A_268,B_265,C_269),B_267)
      | r1_yellow_0(A_268,B_265)
      | ~ r2_lattice3(A_268,B_265,C_269)
      | ~ m1_subset_1(C_269,u1_struct_0(A_268))
      | ~ l1_orders_2(A_268)
      | ~ v5_orders_2(A_268) ) ),
    inference(resolution,[status(thm)],[c_30,c_186])).

tff(c_703,plain,(
    ! [A_319,B_320,C_321] :
      ( r1_orders_2(A_319,'#skF_1'(A_319),'#skF_3'(A_319,B_320,C_321))
      | ~ m1_subset_1('#skF_1'(A_319),u1_struct_0(A_319))
      | v1_xboole_0(u1_struct_0(A_319))
      | ~ m1_subset_1('#skF_3'(A_319,B_320,C_321),u1_struct_0(A_319))
      | r1_yellow_0(A_319,B_320)
      | ~ r2_lattice3(A_319,B_320,C_321)
      | ~ m1_subset_1(C_321,u1_struct_0(A_319))
      | ~ v5_orders_2(A_319)
      | ~ v1_yellow_0(A_319)
      | ~ l1_orders_2(A_319) ) ),
    inference(resolution,[status(thm)],[c_4,c_548])).

tff(c_26,plain,(
    ! [A_19,C_40,B_33] :
      ( ~ r1_orders_2(A_19,C_40,'#skF_3'(A_19,B_33,C_40))
      | r1_yellow_0(A_19,B_33)
      | ~ r2_lattice3(A_19,B_33,C_40)
      | ~ m1_subset_1(C_40,u1_struct_0(A_19))
      | ~ l1_orders_2(A_19)
      | ~ v5_orders_2(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_709,plain,(
    ! [A_322,B_323] :
      ( v1_xboole_0(u1_struct_0(A_322))
      | ~ m1_subset_1('#skF_3'(A_322,B_323,'#skF_1'(A_322)),u1_struct_0(A_322))
      | r1_yellow_0(A_322,B_323)
      | ~ r2_lattice3(A_322,B_323,'#skF_1'(A_322))
      | ~ m1_subset_1('#skF_1'(A_322),u1_struct_0(A_322))
      | ~ v5_orders_2(A_322)
      | ~ v1_yellow_0(A_322)
      | ~ l1_orders_2(A_322) ) ),
    inference(resolution,[status(thm)],[c_703,c_26])).

tff(c_715,plain,(
    ! [A_324,B_325] :
      ( v1_xboole_0(u1_struct_0(A_324))
      | ~ v1_yellow_0(A_324)
      | r1_yellow_0(A_324,B_325)
      | ~ r2_lattice3(A_324,B_325,'#skF_1'(A_324))
      | ~ m1_subset_1('#skF_1'(A_324),u1_struct_0(A_324))
      | ~ l1_orders_2(A_324)
      | ~ v5_orders_2(A_324) ) ),
    inference(resolution,[status(thm)],[c_30,c_709])).

tff(c_720,plain,(
    ! [A_329] :
      ( v1_xboole_0(u1_struct_0(A_329))
      | r1_yellow_0(A_329,k1_xboole_0)
      | ~ m1_subset_1('#skF_1'(A_329),u1_struct_0(A_329))
      | ~ v5_orders_2(A_329)
      | ~ v1_yellow_0(A_329)
      | ~ l1_orders_2(A_329) ) ),
    inference(resolution,[status(thm)],[c_74,c_715])).

tff(c_725,plain,(
    ! [A_330] :
      ( v1_xboole_0(u1_struct_0(A_330))
      | r1_yellow_0(A_330,k1_xboole_0)
      | ~ v5_orders_2(A_330)
      | ~ v1_yellow_0(A_330)
      | ~ l1_orders_2(A_330) ) ),
    inference(resolution,[status(thm)],[c_6,c_720])).

tff(c_18,plain,(
    ! [A_18] :
      ( ~ v1_xboole_0(u1_struct_0(A_18))
      | ~ l1_struct_0(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_730,plain,(
    ! [A_331] :
      ( ~ l1_struct_0(A_331)
      | v2_struct_0(A_331)
      | r1_yellow_0(A_331,k1_xboole_0)
      | ~ v5_orders_2(A_331)
      | ~ v1_yellow_0(A_331)
      | ~ l1_orders_2(A_331) ) ),
    inference(resolution,[status(thm)],[c_725,c_18])).

tff(c_50,plain,
    ( ~ r2_yellow_0('#skF_7',u1_struct_0('#skF_7'))
    | ~ r1_yellow_0('#skF_7',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_61,plain,(
    ~ r1_yellow_0('#skF_7',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_736,plain,
    ( ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7')
    | ~ v5_orders_2('#skF_7')
    | ~ v1_yellow_0('#skF_7')
    | ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_730,c_61])).

tff(c_740,plain,
    ( ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_54,c_56,c_736])).

tff(c_741,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_740])).

tff(c_744,plain,(
    ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_16,c_741])).

tff(c_748,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_744])).

tff(c_749,plain,(
    ~ r2_yellow_0('#skF_7',u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1384,plain,
    ( v1_xboole_0(u1_struct_0('#skF_7'))
    | ~ v5_orders_2('#skF_7')
    | ~ v1_yellow_0('#skF_7')
    | ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_1378,c_749])).

tff(c_1388,plain,(
    v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_54,c_56,c_1384])).

tff(c_1391,plain,
    ( ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_1388,c_18])).

tff(c_1394,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1391])).

tff(c_1397,plain,(
    ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_16,c_1394])).

tff(c_1401,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1397])).

%------------------------------------------------------------------------------
