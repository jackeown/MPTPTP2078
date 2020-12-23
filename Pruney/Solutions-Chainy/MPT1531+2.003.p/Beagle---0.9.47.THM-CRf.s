%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:59 EST 2020

% Result     : Theorem 4.00s
% Output     : CNFRefutation 4.47s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 138 expanded)
%              Number of leaves         :   23 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :  217 ( 479 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_tarski > m1_subset_1 > l1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => ! [B,C] :
            ( r1_tarski(B,C)
           => ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( ( r1_lattice3(A,C,D)
                   => r1_lattice3(A,B,D) )
                  & ( r2_lattice3(A,C,D)
                   => r2_lattice3(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r2_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r1_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

tff(c_26,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_24,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_28,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_36,plain,
    ( r1_lattice3('#skF_3','#skF_5','#skF_6')
    | r2_lattice3('#skF_3','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_43,plain,(
    r2_lattice3('#skF_3','#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_22,plain,(
    ! [A_19,B_26,C_27] :
      ( m1_subset_1('#skF_2'(A_19,B_26,C_27),u1_struct_0(A_19))
      | r2_lattice3(A_19,B_26,C_27)
      | ~ m1_subset_1(C_27,u1_struct_0(A_19))
      | ~ l1_orders_2(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_51,plain,(
    ! [A_46,B_47,C_48] :
      ( r2_hidden('#skF_2'(A_46,B_47,C_48),B_47)
      | r2_lattice3(A_46,B_47,C_48)
      | ~ m1_subset_1(C_48,u1_struct_0(A_46))
      | ~ l1_orders_2(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_54,plain,(
    ! [A_46,B_47,C_48,A_1] :
      ( r2_hidden('#skF_2'(A_46,B_47,C_48),A_1)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_1))
      | r2_lattice3(A_46,B_47,C_48)
      | ~ m1_subset_1(C_48,u1_struct_0(A_46))
      | ~ l1_orders_2(A_46) ) ),
    inference(resolution,[status(thm)],[c_51,c_2])).

tff(c_80,plain,(
    ! [A_73,D_74,C_75,B_76] :
      ( r1_orders_2(A_73,D_74,C_75)
      | ~ r2_hidden(D_74,B_76)
      | ~ m1_subset_1(D_74,u1_struct_0(A_73))
      | ~ r2_lattice3(A_73,B_76,C_75)
      | ~ m1_subset_1(C_75,u1_struct_0(A_73))
      | ~ l1_orders_2(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_353,plain,(
    ! [A_303,C_299,C_300,B_298,A_302,A_301] :
      ( r1_orders_2(A_302,'#skF_2'(A_303,B_298,C_300),C_299)
      | ~ m1_subset_1('#skF_2'(A_303,B_298,C_300),u1_struct_0(A_302))
      | ~ r2_lattice3(A_302,A_301,C_299)
      | ~ m1_subset_1(C_299,u1_struct_0(A_302))
      | ~ l1_orders_2(A_302)
      | ~ m1_subset_1(B_298,k1_zfmisc_1(A_301))
      | r2_lattice3(A_303,B_298,C_300)
      | ~ m1_subset_1(C_300,u1_struct_0(A_303))
      | ~ l1_orders_2(A_303) ) ),
    inference(resolution,[status(thm)],[c_54,c_80])).

tff(c_357,plain,(
    ! [A_308,C_305,B_307,A_306,C_304] :
      ( r1_orders_2(A_306,'#skF_2'(A_306,B_307,C_305),C_304)
      | ~ r2_lattice3(A_306,A_308,C_304)
      | ~ m1_subset_1(C_304,u1_struct_0(A_306))
      | ~ m1_subset_1(B_307,k1_zfmisc_1(A_308))
      | r2_lattice3(A_306,B_307,C_305)
      | ~ m1_subset_1(C_305,u1_struct_0(A_306))
      | ~ l1_orders_2(A_306) ) ),
    inference(resolution,[status(thm)],[c_22,c_353])).

tff(c_361,plain,(
    ! [B_307,C_305] :
      ( r1_orders_2('#skF_3','#skF_2'('#skF_3',B_307,C_305),'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_307,k1_zfmisc_1('#skF_5'))
      | r2_lattice3('#skF_3',B_307,C_305)
      | ~ m1_subset_1(C_305,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_43,c_357])).

tff(c_368,plain,(
    ! [B_309,C_310] :
      ( r1_orders_2('#skF_3','#skF_2'('#skF_3',B_309,C_310),'#skF_6')
      | ~ m1_subset_1(B_309,k1_zfmisc_1('#skF_5'))
      | r2_lattice3('#skF_3',B_309,C_310)
      | ~ m1_subset_1(C_310,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_361])).

tff(c_18,plain,(
    ! [A_19,B_26,C_27] :
      ( ~ r1_orders_2(A_19,'#skF_2'(A_19,B_26,C_27),C_27)
      | r2_lattice3(A_19,B_26,C_27)
      | ~ m1_subset_1(C_27,u1_struct_0(A_19))
      | ~ l1_orders_2(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_372,plain,(
    ! [B_309] :
      ( ~ l1_orders_2('#skF_3')
      | ~ m1_subset_1(B_309,k1_zfmisc_1('#skF_5'))
      | r2_lattice3('#skF_3',B_309,'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_368,c_18])).

tff(c_376,plain,(
    ! [B_311] :
      ( ~ m1_subset_1(B_311,k1_zfmisc_1('#skF_5'))
      | r2_lattice3('#skF_3',B_311,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28,c_372])).

tff(c_386,plain,(
    ! [A_318] :
      ( r2_lattice3('#skF_3',A_318,'#skF_6')
      | ~ r1_tarski(A_318,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6,c_376])).

tff(c_30,plain,
    ( ~ r1_lattice3('#skF_3','#skF_4','#skF_6')
    | ~ r2_lattice3('#skF_3','#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_44,plain,(
    ~ r2_lattice3('#skF_3','#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_393,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_386,c_44])).

tff(c_403,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_393])).

tff(c_405,plain,(
    r2_lattice3('#skF_3','#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_32,plain,
    ( r1_lattice3('#skF_3','#skF_5','#skF_6')
    | ~ r2_lattice3('#skF_3','#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_408,plain,(
    r1_lattice3('#skF_3','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_405,c_32])).

tff(c_14,plain,(
    ! [A_7,B_14,C_15] :
      ( m1_subset_1('#skF_1'(A_7,B_14,C_15),u1_struct_0(A_7))
      | r1_lattice3(A_7,B_14,C_15)
      | ~ m1_subset_1(C_15,u1_struct_0(A_7))
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_414,plain,(
    ! [A_325,B_326,C_327] :
      ( r2_hidden('#skF_1'(A_325,B_326,C_327),B_326)
      | r1_lattice3(A_325,B_326,C_327)
      | ~ m1_subset_1(C_327,u1_struct_0(A_325))
      | ~ l1_orders_2(A_325) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_417,plain,(
    ! [A_325,B_326,C_327,A_1] :
      ( r2_hidden('#skF_1'(A_325,B_326,C_327),A_1)
      | ~ m1_subset_1(B_326,k1_zfmisc_1(A_1))
      | r1_lattice3(A_325,B_326,C_327)
      | ~ m1_subset_1(C_327,u1_struct_0(A_325))
      | ~ l1_orders_2(A_325) ) ),
    inference(resolution,[status(thm)],[c_414,c_2])).

tff(c_430,plain,(
    ! [A_348,C_349,D_350,B_351] :
      ( r1_orders_2(A_348,C_349,D_350)
      | ~ r2_hidden(D_350,B_351)
      | ~ m1_subset_1(D_350,u1_struct_0(A_348))
      | ~ r1_lattice3(A_348,B_351,C_349)
      | ~ m1_subset_1(C_349,u1_struct_0(A_348))
      | ~ l1_orders_2(A_348) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_673,plain,(
    ! [C_518,C_521,A_522,A_519,B_523,A_520] :
      ( r1_orders_2(A_520,C_518,'#skF_1'(A_519,B_523,C_521))
      | ~ m1_subset_1('#skF_1'(A_519,B_523,C_521),u1_struct_0(A_520))
      | ~ r1_lattice3(A_520,A_522,C_518)
      | ~ m1_subset_1(C_518,u1_struct_0(A_520))
      | ~ l1_orders_2(A_520)
      | ~ m1_subset_1(B_523,k1_zfmisc_1(A_522))
      | r1_lattice3(A_519,B_523,C_521)
      | ~ m1_subset_1(C_521,u1_struct_0(A_519))
      | ~ l1_orders_2(A_519) ) ),
    inference(resolution,[status(thm)],[c_417,c_430])).

tff(c_684,plain,(
    ! [C_535,B_532,A_536,C_533,A_534] :
      ( r1_orders_2(A_534,C_533,'#skF_1'(A_534,B_532,C_535))
      | ~ r1_lattice3(A_534,A_536,C_533)
      | ~ m1_subset_1(C_533,u1_struct_0(A_534))
      | ~ m1_subset_1(B_532,k1_zfmisc_1(A_536))
      | r1_lattice3(A_534,B_532,C_535)
      | ~ m1_subset_1(C_535,u1_struct_0(A_534))
      | ~ l1_orders_2(A_534) ) ),
    inference(resolution,[status(thm)],[c_14,c_673])).

tff(c_688,plain,(
    ! [B_532,C_535] :
      ( r1_orders_2('#skF_3','#skF_6','#skF_1'('#skF_3',B_532,C_535))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_532,k1_zfmisc_1('#skF_5'))
      | r1_lattice3('#skF_3',B_532,C_535)
      | ~ m1_subset_1(C_535,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_408,c_684])).

tff(c_695,plain,(
    ! [B_537,C_538] :
      ( r1_orders_2('#skF_3','#skF_6','#skF_1'('#skF_3',B_537,C_538))
      | ~ m1_subset_1(B_537,k1_zfmisc_1('#skF_5'))
      | r1_lattice3('#skF_3',B_537,C_538)
      | ~ m1_subset_1(C_538,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_688])).

tff(c_10,plain,(
    ! [A_7,C_15,B_14] :
      ( ~ r1_orders_2(A_7,C_15,'#skF_1'(A_7,B_14,C_15))
      | r1_lattice3(A_7,B_14,C_15)
      | ~ m1_subset_1(C_15,u1_struct_0(A_7))
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_699,plain,(
    ! [B_537] :
      ( ~ l1_orders_2('#skF_3')
      | ~ m1_subset_1(B_537,k1_zfmisc_1('#skF_5'))
      | r1_lattice3('#skF_3',B_537,'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_695,c_10])).

tff(c_703,plain,(
    ! [B_539] :
      ( ~ m1_subset_1(B_539,k1_zfmisc_1('#skF_5'))
      | r1_lattice3('#skF_3',B_539,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28,c_699])).

tff(c_709,plain,(
    ! [A_540] :
      ( r1_lattice3('#skF_3',A_540,'#skF_6')
      | ~ r1_tarski(A_540,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6,c_703])).

tff(c_404,plain,(
    ~ r1_lattice3('#skF_3','#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_714,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_709,c_404])).

tff(c_721,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_714])).

tff(c_722,plain,(
    r1_lattice3('#skF_3','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_728,plain,(
    ! [A_544,B_545,C_546] :
      ( r2_hidden('#skF_1'(A_544,B_545,C_546),B_545)
      | r1_lattice3(A_544,B_545,C_546)
      | ~ m1_subset_1(C_546,u1_struct_0(A_544))
      | ~ l1_orders_2(A_544) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_754,plain,(
    ! [A_570,B_571,C_572,A_573] :
      ( r2_hidden('#skF_1'(A_570,B_571,C_572),A_573)
      | ~ m1_subset_1(B_571,k1_zfmisc_1(A_573))
      | r1_lattice3(A_570,B_571,C_572)
      | ~ m1_subset_1(C_572,u1_struct_0(A_570))
      | ~ l1_orders_2(A_570) ) ),
    inference(resolution,[status(thm)],[c_728,c_2])).

tff(c_8,plain,(
    ! [A_7,C_15,D_18,B_14] :
      ( r1_orders_2(A_7,C_15,D_18)
      | ~ r2_hidden(D_18,B_14)
      | ~ m1_subset_1(D_18,u1_struct_0(A_7))
      | ~ r1_lattice3(A_7,B_14,C_15)
      | ~ m1_subset_1(C_15,u1_struct_0(A_7))
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1007,plain,(
    ! [A_771,A_772,C_773,B_770,A_774,C_769] :
      ( r1_orders_2(A_771,C_773,'#skF_1'(A_774,B_770,C_769))
      | ~ m1_subset_1('#skF_1'(A_774,B_770,C_769),u1_struct_0(A_771))
      | ~ r1_lattice3(A_771,A_772,C_773)
      | ~ m1_subset_1(C_773,u1_struct_0(A_771))
      | ~ l1_orders_2(A_771)
      | ~ m1_subset_1(B_770,k1_zfmisc_1(A_772))
      | r1_lattice3(A_774,B_770,C_769)
      | ~ m1_subset_1(C_769,u1_struct_0(A_774))
      | ~ l1_orders_2(A_774) ) ),
    inference(resolution,[status(thm)],[c_754,c_8])).

tff(c_1011,plain,(
    ! [A_778,C_779,A_777,C_776,B_775] :
      ( r1_orders_2(A_777,C_776,'#skF_1'(A_777,B_775,C_779))
      | ~ r1_lattice3(A_777,A_778,C_776)
      | ~ m1_subset_1(C_776,u1_struct_0(A_777))
      | ~ m1_subset_1(B_775,k1_zfmisc_1(A_778))
      | r1_lattice3(A_777,B_775,C_779)
      | ~ m1_subset_1(C_779,u1_struct_0(A_777))
      | ~ l1_orders_2(A_777) ) ),
    inference(resolution,[status(thm)],[c_14,c_1007])).

tff(c_1015,plain,(
    ! [B_775,C_779] :
      ( r1_orders_2('#skF_3','#skF_6','#skF_1'('#skF_3',B_775,C_779))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_775,k1_zfmisc_1('#skF_5'))
      | r1_lattice3('#skF_3',B_775,C_779)
      | ~ m1_subset_1(C_779,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_722,c_1011])).

tff(c_1026,plain,(
    ! [B_786,C_787] :
      ( r1_orders_2('#skF_3','#skF_6','#skF_1'('#skF_3',B_786,C_787))
      | ~ m1_subset_1(B_786,k1_zfmisc_1('#skF_5'))
      | r1_lattice3('#skF_3',B_786,C_787)
      | ~ m1_subset_1(C_787,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_1015])).

tff(c_1030,plain,(
    ! [B_786] :
      ( ~ l1_orders_2('#skF_3')
      | ~ m1_subset_1(B_786,k1_zfmisc_1('#skF_5'))
      | r1_lattice3('#skF_3',B_786,'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1026,c_10])).

tff(c_1034,plain,(
    ! [B_788] :
      ( ~ m1_subset_1(B_788,k1_zfmisc_1('#skF_5'))
      | r1_lattice3('#skF_3',B_788,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28,c_1030])).

tff(c_1040,plain,(
    ! [A_789] :
      ( r1_lattice3('#skF_3',A_789,'#skF_6')
      | ~ r1_tarski(A_789,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6,c_1034])).

tff(c_723,plain,(
    ~ r2_lattice3('#skF_3','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_34,plain,
    ( ~ r1_lattice3('#skF_3','#skF_4','#skF_6')
    | r2_lattice3('#skF_3','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_726,plain,(
    ~ r1_lattice3('#skF_3','#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_723,c_34])).

tff(c_1045,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_1040,c_726])).

tff(c_1052,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1045])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:55:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.00/1.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.00/1.78  
% 4.00/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.00/1.78  %$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_tarski > m1_subset_1 > l1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 4.00/1.78  
% 4.00/1.78  %Foreground sorts:
% 4.00/1.78  
% 4.00/1.78  
% 4.00/1.78  %Background operators:
% 4.00/1.78  
% 4.00/1.78  
% 4.00/1.78  %Foreground operators:
% 4.00/1.78  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.00/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.00/1.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.00/1.78  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 4.00/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.00/1.78  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 4.00/1.78  tff('#skF_5', type, '#skF_5': $i).
% 4.00/1.78  tff('#skF_6', type, '#skF_6': $i).
% 4.00/1.78  tff('#skF_3', type, '#skF_3': $i).
% 4.00/1.78  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.00/1.78  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 4.00/1.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.00/1.78  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.00/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.00/1.78  tff('#skF_4', type, '#skF_4': $i).
% 4.00/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.00/1.78  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.00/1.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.00/1.78  
% 4.47/1.81  tff(f_81, negated_conjecture, ~(![A]: (l1_orders_2(A) => (![B, C]: (r1_tarski(B, C) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r1_lattice3(A, C, D) => r1_lattice3(A, B, D)) & (r2_lattice3(A, C, D) => r2_lattice3(A, B, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_yellow_0)).
% 4.47/1.81  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.47/1.81  tff(f_64, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, D, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 4.47/1.81  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 4.47/1.81  tff(f_50, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattice3)).
% 4.47/1.81  tff(c_26, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.47/1.81  tff(c_6, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.47/1.81  tff(c_24, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.47/1.81  tff(c_28, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.47/1.81  tff(c_36, plain, (r1_lattice3('#skF_3', '#skF_5', '#skF_6') | r2_lattice3('#skF_3', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.47/1.81  tff(c_43, plain, (r2_lattice3('#skF_3', '#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_36])).
% 4.47/1.81  tff(c_22, plain, (![A_19, B_26, C_27]: (m1_subset_1('#skF_2'(A_19, B_26, C_27), u1_struct_0(A_19)) | r2_lattice3(A_19, B_26, C_27) | ~m1_subset_1(C_27, u1_struct_0(A_19)) | ~l1_orders_2(A_19))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.47/1.81  tff(c_51, plain, (![A_46, B_47, C_48]: (r2_hidden('#skF_2'(A_46, B_47, C_48), B_47) | r2_lattice3(A_46, B_47, C_48) | ~m1_subset_1(C_48, u1_struct_0(A_46)) | ~l1_orders_2(A_46))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.47/1.81  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.47/1.81  tff(c_54, plain, (![A_46, B_47, C_48, A_1]: (r2_hidden('#skF_2'(A_46, B_47, C_48), A_1) | ~m1_subset_1(B_47, k1_zfmisc_1(A_1)) | r2_lattice3(A_46, B_47, C_48) | ~m1_subset_1(C_48, u1_struct_0(A_46)) | ~l1_orders_2(A_46))), inference(resolution, [status(thm)], [c_51, c_2])).
% 4.47/1.81  tff(c_80, plain, (![A_73, D_74, C_75, B_76]: (r1_orders_2(A_73, D_74, C_75) | ~r2_hidden(D_74, B_76) | ~m1_subset_1(D_74, u1_struct_0(A_73)) | ~r2_lattice3(A_73, B_76, C_75) | ~m1_subset_1(C_75, u1_struct_0(A_73)) | ~l1_orders_2(A_73))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.47/1.81  tff(c_353, plain, (![A_303, C_299, C_300, B_298, A_302, A_301]: (r1_orders_2(A_302, '#skF_2'(A_303, B_298, C_300), C_299) | ~m1_subset_1('#skF_2'(A_303, B_298, C_300), u1_struct_0(A_302)) | ~r2_lattice3(A_302, A_301, C_299) | ~m1_subset_1(C_299, u1_struct_0(A_302)) | ~l1_orders_2(A_302) | ~m1_subset_1(B_298, k1_zfmisc_1(A_301)) | r2_lattice3(A_303, B_298, C_300) | ~m1_subset_1(C_300, u1_struct_0(A_303)) | ~l1_orders_2(A_303))), inference(resolution, [status(thm)], [c_54, c_80])).
% 4.47/1.81  tff(c_357, plain, (![A_308, C_305, B_307, A_306, C_304]: (r1_orders_2(A_306, '#skF_2'(A_306, B_307, C_305), C_304) | ~r2_lattice3(A_306, A_308, C_304) | ~m1_subset_1(C_304, u1_struct_0(A_306)) | ~m1_subset_1(B_307, k1_zfmisc_1(A_308)) | r2_lattice3(A_306, B_307, C_305) | ~m1_subset_1(C_305, u1_struct_0(A_306)) | ~l1_orders_2(A_306))), inference(resolution, [status(thm)], [c_22, c_353])).
% 4.47/1.81  tff(c_361, plain, (![B_307, C_305]: (r1_orders_2('#skF_3', '#skF_2'('#skF_3', B_307, C_305), '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1(B_307, k1_zfmisc_1('#skF_5')) | r2_lattice3('#skF_3', B_307, C_305) | ~m1_subset_1(C_305, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_43, c_357])).
% 4.47/1.81  tff(c_368, plain, (![B_309, C_310]: (r1_orders_2('#skF_3', '#skF_2'('#skF_3', B_309, C_310), '#skF_6') | ~m1_subset_1(B_309, k1_zfmisc_1('#skF_5')) | r2_lattice3('#skF_3', B_309, C_310) | ~m1_subset_1(C_310, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_361])).
% 4.47/1.81  tff(c_18, plain, (![A_19, B_26, C_27]: (~r1_orders_2(A_19, '#skF_2'(A_19, B_26, C_27), C_27) | r2_lattice3(A_19, B_26, C_27) | ~m1_subset_1(C_27, u1_struct_0(A_19)) | ~l1_orders_2(A_19))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.47/1.81  tff(c_372, plain, (![B_309]: (~l1_orders_2('#skF_3') | ~m1_subset_1(B_309, k1_zfmisc_1('#skF_5')) | r2_lattice3('#skF_3', B_309, '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_368, c_18])).
% 4.47/1.81  tff(c_376, plain, (![B_311]: (~m1_subset_1(B_311, k1_zfmisc_1('#skF_5')) | r2_lattice3('#skF_3', B_311, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_28, c_372])).
% 4.47/1.81  tff(c_386, plain, (![A_318]: (r2_lattice3('#skF_3', A_318, '#skF_6') | ~r1_tarski(A_318, '#skF_5'))), inference(resolution, [status(thm)], [c_6, c_376])).
% 4.47/1.81  tff(c_30, plain, (~r1_lattice3('#skF_3', '#skF_4', '#skF_6') | ~r2_lattice3('#skF_3', '#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.47/1.81  tff(c_44, plain, (~r2_lattice3('#skF_3', '#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_30])).
% 4.47/1.81  tff(c_393, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_386, c_44])).
% 4.47/1.81  tff(c_403, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_393])).
% 4.47/1.81  tff(c_405, plain, (r2_lattice3('#skF_3', '#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_30])).
% 4.47/1.81  tff(c_32, plain, (r1_lattice3('#skF_3', '#skF_5', '#skF_6') | ~r2_lattice3('#skF_3', '#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.47/1.81  tff(c_408, plain, (r1_lattice3('#skF_3', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_405, c_32])).
% 4.47/1.81  tff(c_14, plain, (![A_7, B_14, C_15]: (m1_subset_1('#skF_1'(A_7, B_14, C_15), u1_struct_0(A_7)) | r1_lattice3(A_7, B_14, C_15) | ~m1_subset_1(C_15, u1_struct_0(A_7)) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.47/1.81  tff(c_414, plain, (![A_325, B_326, C_327]: (r2_hidden('#skF_1'(A_325, B_326, C_327), B_326) | r1_lattice3(A_325, B_326, C_327) | ~m1_subset_1(C_327, u1_struct_0(A_325)) | ~l1_orders_2(A_325))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.47/1.81  tff(c_417, plain, (![A_325, B_326, C_327, A_1]: (r2_hidden('#skF_1'(A_325, B_326, C_327), A_1) | ~m1_subset_1(B_326, k1_zfmisc_1(A_1)) | r1_lattice3(A_325, B_326, C_327) | ~m1_subset_1(C_327, u1_struct_0(A_325)) | ~l1_orders_2(A_325))), inference(resolution, [status(thm)], [c_414, c_2])).
% 4.47/1.81  tff(c_430, plain, (![A_348, C_349, D_350, B_351]: (r1_orders_2(A_348, C_349, D_350) | ~r2_hidden(D_350, B_351) | ~m1_subset_1(D_350, u1_struct_0(A_348)) | ~r1_lattice3(A_348, B_351, C_349) | ~m1_subset_1(C_349, u1_struct_0(A_348)) | ~l1_orders_2(A_348))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.47/1.81  tff(c_673, plain, (![C_518, C_521, A_522, A_519, B_523, A_520]: (r1_orders_2(A_520, C_518, '#skF_1'(A_519, B_523, C_521)) | ~m1_subset_1('#skF_1'(A_519, B_523, C_521), u1_struct_0(A_520)) | ~r1_lattice3(A_520, A_522, C_518) | ~m1_subset_1(C_518, u1_struct_0(A_520)) | ~l1_orders_2(A_520) | ~m1_subset_1(B_523, k1_zfmisc_1(A_522)) | r1_lattice3(A_519, B_523, C_521) | ~m1_subset_1(C_521, u1_struct_0(A_519)) | ~l1_orders_2(A_519))), inference(resolution, [status(thm)], [c_417, c_430])).
% 4.47/1.81  tff(c_684, plain, (![C_535, B_532, A_536, C_533, A_534]: (r1_orders_2(A_534, C_533, '#skF_1'(A_534, B_532, C_535)) | ~r1_lattice3(A_534, A_536, C_533) | ~m1_subset_1(C_533, u1_struct_0(A_534)) | ~m1_subset_1(B_532, k1_zfmisc_1(A_536)) | r1_lattice3(A_534, B_532, C_535) | ~m1_subset_1(C_535, u1_struct_0(A_534)) | ~l1_orders_2(A_534))), inference(resolution, [status(thm)], [c_14, c_673])).
% 4.47/1.81  tff(c_688, plain, (![B_532, C_535]: (r1_orders_2('#skF_3', '#skF_6', '#skF_1'('#skF_3', B_532, C_535)) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1(B_532, k1_zfmisc_1('#skF_5')) | r1_lattice3('#skF_3', B_532, C_535) | ~m1_subset_1(C_535, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_408, c_684])).
% 4.47/1.81  tff(c_695, plain, (![B_537, C_538]: (r1_orders_2('#skF_3', '#skF_6', '#skF_1'('#skF_3', B_537, C_538)) | ~m1_subset_1(B_537, k1_zfmisc_1('#skF_5')) | r1_lattice3('#skF_3', B_537, C_538) | ~m1_subset_1(C_538, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_688])).
% 4.47/1.81  tff(c_10, plain, (![A_7, C_15, B_14]: (~r1_orders_2(A_7, C_15, '#skF_1'(A_7, B_14, C_15)) | r1_lattice3(A_7, B_14, C_15) | ~m1_subset_1(C_15, u1_struct_0(A_7)) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.47/1.81  tff(c_699, plain, (![B_537]: (~l1_orders_2('#skF_3') | ~m1_subset_1(B_537, k1_zfmisc_1('#skF_5')) | r1_lattice3('#skF_3', B_537, '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_695, c_10])).
% 4.47/1.81  tff(c_703, plain, (![B_539]: (~m1_subset_1(B_539, k1_zfmisc_1('#skF_5')) | r1_lattice3('#skF_3', B_539, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_28, c_699])).
% 4.47/1.81  tff(c_709, plain, (![A_540]: (r1_lattice3('#skF_3', A_540, '#skF_6') | ~r1_tarski(A_540, '#skF_5'))), inference(resolution, [status(thm)], [c_6, c_703])).
% 4.47/1.81  tff(c_404, plain, (~r1_lattice3('#skF_3', '#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_30])).
% 4.47/1.81  tff(c_714, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_709, c_404])).
% 4.47/1.81  tff(c_721, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_714])).
% 4.47/1.81  tff(c_722, plain, (r1_lattice3('#skF_3', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_36])).
% 4.47/1.81  tff(c_728, plain, (![A_544, B_545, C_546]: (r2_hidden('#skF_1'(A_544, B_545, C_546), B_545) | r1_lattice3(A_544, B_545, C_546) | ~m1_subset_1(C_546, u1_struct_0(A_544)) | ~l1_orders_2(A_544))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.47/1.81  tff(c_754, plain, (![A_570, B_571, C_572, A_573]: (r2_hidden('#skF_1'(A_570, B_571, C_572), A_573) | ~m1_subset_1(B_571, k1_zfmisc_1(A_573)) | r1_lattice3(A_570, B_571, C_572) | ~m1_subset_1(C_572, u1_struct_0(A_570)) | ~l1_orders_2(A_570))), inference(resolution, [status(thm)], [c_728, c_2])).
% 4.47/1.81  tff(c_8, plain, (![A_7, C_15, D_18, B_14]: (r1_orders_2(A_7, C_15, D_18) | ~r2_hidden(D_18, B_14) | ~m1_subset_1(D_18, u1_struct_0(A_7)) | ~r1_lattice3(A_7, B_14, C_15) | ~m1_subset_1(C_15, u1_struct_0(A_7)) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.47/1.81  tff(c_1007, plain, (![A_771, A_772, C_773, B_770, A_774, C_769]: (r1_orders_2(A_771, C_773, '#skF_1'(A_774, B_770, C_769)) | ~m1_subset_1('#skF_1'(A_774, B_770, C_769), u1_struct_0(A_771)) | ~r1_lattice3(A_771, A_772, C_773) | ~m1_subset_1(C_773, u1_struct_0(A_771)) | ~l1_orders_2(A_771) | ~m1_subset_1(B_770, k1_zfmisc_1(A_772)) | r1_lattice3(A_774, B_770, C_769) | ~m1_subset_1(C_769, u1_struct_0(A_774)) | ~l1_orders_2(A_774))), inference(resolution, [status(thm)], [c_754, c_8])).
% 4.47/1.81  tff(c_1011, plain, (![A_778, C_779, A_777, C_776, B_775]: (r1_orders_2(A_777, C_776, '#skF_1'(A_777, B_775, C_779)) | ~r1_lattice3(A_777, A_778, C_776) | ~m1_subset_1(C_776, u1_struct_0(A_777)) | ~m1_subset_1(B_775, k1_zfmisc_1(A_778)) | r1_lattice3(A_777, B_775, C_779) | ~m1_subset_1(C_779, u1_struct_0(A_777)) | ~l1_orders_2(A_777))), inference(resolution, [status(thm)], [c_14, c_1007])).
% 4.47/1.81  tff(c_1015, plain, (![B_775, C_779]: (r1_orders_2('#skF_3', '#skF_6', '#skF_1'('#skF_3', B_775, C_779)) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1(B_775, k1_zfmisc_1('#skF_5')) | r1_lattice3('#skF_3', B_775, C_779) | ~m1_subset_1(C_779, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_722, c_1011])).
% 4.47/1.81  tff(c_1026, plain, (![B_786, C_787]: (r1_orders_2('#skF_3', '#skF_6', '#skF_1'('#skF_3', B_786, C_787)) | ~m1_subset_1(B_786, k1_zfmisc_1('#skF_5')) | r1_lattice3('#skF_3', B_786, C_787) | ~m1_subset_1(C_787, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_1015])).
% 4.47/1.81  tff(c_1030, plain, (![B_786]: (~l1_orders_2('#skF_3') | ~m1_subset_1(B_786, k1_zfmisc_1('#skF_5')) | r1_lattice3('#skF_3', B_786, '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_1026, c_10])).
% 4.47/1.81  tff(c_1034, plain, (![B_788]: (~m1_subset_1(B_788, k1_zfmisc_1('#skF_5')) | r1_lattice3('#skF_3', B_788, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_28, c_1030])).
% 4.47/1.81  tff(c_1040, plain, (![A_789]: (r1_lattice3('#skF_3', A_789, '#skF_6') | ~r1_tarski(A_789, '#skF_5'))), inference(resolution, [status(thm)], [c_6, c_1034])).
% 4.47/1.81  tff(c_723, plain, (~r2_lattice3('#skF_3', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_36])).
% 4.47/1.81  tff(c_34, plain, (~r1_lattice3('#skF_3', '#skF_4', '#skF_6') | r2_lattice3('#skF_3', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.47/1.81  tff(c_726, plain, (~r1_lattice3('#skF_3', '#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_723, c_34])).
% 4.47/1.81  tff(c_1045, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_1040, c_726])).
% 4.47/1.81  tff(c_1052, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_1045])).
% 4.47/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.47/1.81  
% 4.47/1.81  Inference rules
% 4.47/1.81  ----------------------
% 4.47/1.81  #Ref     : 0
% 4.47/1.81  #Sup     : 223
% 4.47/1.81  #Fact    : 0
% 4.47/1.81  #Define  : 0
% 4.47/1.81  #Split   : 4
% 4.47/1.81  #Chain   : 0
% 4.47/1.81  #Close   : 0
% 4.47/1.81  
% 4.47/1.81  Ordering : KBO
% 4.47/1.81  
% 4.47/1.81  Simplification rules
% 4.47/1.81  ----------------------
% 4.47/1.81  #Subsume      : 10
% 4.47/1.81  #Demod        : 47
% 4.47/1.81  #Tautology    : 8
% 4.47/1.81  #SimpNegUnit  : 1
% 4.47/1.81  #BackRed      : 0
% 4.47/1.81  
% 4.47/1.81  #Partial instantiations: 0
% 4.47/1.81  #Strategies tried      : 1
% 4.47/1.81  
% 4.47/1.81  Timing (in seconds)
% 4.47/1.81  ----------------------
% 4.47/1.81  Preprocessing        : 0.30
% 4.47/1.81  Parsing              : 0.17
% 4.47/1.81  CNF conversion       : 0.02
% 4.47/1.81  Main loop            : 0.70
% 4.47/1.81  Inferencing          : 0.31
% 4.47/1.81  Reduction            : 0.14
% 4.47/1.81  Demodulation         : 0.08
% 4.47/1.81  BG Simplification    : 0.03
% 4.47/1.81  Subsumption          : 0.17
% 4.47/1.81  Abstraction          : 0.03
% 4.47/1.81  MUC search           : 0.00
% 4.47/1.81  Cooper               : 0.00
% 4.47/1.81  Total                : 1.04
% 4.47/1.81  Index Insertion      : 0.00
% 4.47/1.81  Index Deletion       : 0.00
% 4.47/1.81  Index Matching       : 0.00
% 4.47/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
