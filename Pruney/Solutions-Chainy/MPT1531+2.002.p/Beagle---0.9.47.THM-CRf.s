%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:58 EST 2020

% Result     : Theorem 4.15s
% Output     : CNFRefutation 4.15s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 137 expanded)
%              Number of leaves         :   22 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :  227 ( 475 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_tarski > m1_subset_1 > l1_orders_2 > #nlpp > u1_struct_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_77,negated_conjecture,(
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

tff(f_60,axiom,(
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

tff(f_46,axiom,(
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

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_868,plain,(
    ! [A_555,B_556] :
      ( ~ r2_hidden('#skF_1'(A_555,B_556),B_556)
      | r1_tarski(A_555,B_556) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_873,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_868])).

tff(c_28,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_26,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_24,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_39,plain,(
    ! [A_37,B_38] :
      ( ~ r2_hidden('#skF_1'(A_37,B_38),B_38)
      | r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_44,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_39])).

tff(c_36,plain,
    ( r1_lattice3('#skF_4','#skF_6','#skF_7')
    | r2_lattice3('#skF_4','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_37,plain,(
    r2_lattice3('#skF_4','#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_22,plain,(
    ! [A_18,B_25,C_26] :
      ( m1_subset_1('#skF_3'(A_18,B_25,C_26),u1_struct_0(A_18))
      | r2_lattice3(A_18,B_25,C_26)
      | ~ m1_subset_1(C_26,u1_struct_0(A_18))
      | ~ l1_orders_2(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_68,plain,(
    ! [A_50,B_51,C_52] :
      ( r2_hidden('#skF_3'(A_50,B_51,C_52),B_51)
      | r2_lattice3(A_50,B_51,C_52)
      | ~ m1_subset_1(C_52,u1_struct_0(A_50))
      | ~ l1_orders_2(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_136,plain,(
    ! [A_84,B_85,C_86,B_87] :
      ( r2_hidden('#skF_3'(A_84,B_85,C_86),B_87)
      | ~ r1_tarski(B_85,B_87)
      | r2_lattice3(A_84,B_85,C_86)
      | ~ m1_subset_1(C_86,u1_struct_0(A_84))
      | ~ l1_orders_2(A_84) ) ),
    inference(resolution,[status(thm)],[c_68,c_2])).

tff(c_193,plain,(
    ! [B_111,C_108,A_110,B_109,B_112] :
      ( r2_hidden('#skF_3'(A_110,B_111,C_108),B_112)
      | ~ r1_tarski(B_109,B_112)
      | ~ r1_tarski(B_111,B_109)
      | r2_lattice3(A_110,B_111,C_108)
      | ~ m1_subset_1(C_108,u1_struct_0(A_110))
      | ~ l1_orders_2(A_110) ) ),
    inference(resolution,[status(thm)],[c_136,c_2])).

tff(c_200,plain,(
    ! [A_113,B_114,C_115] :
      ( r2_hidden('#skF_3'(A_113,B_114,C_115),'#skF_6')
      | ~ r1_tarski(B_114,'#skF_5')
      | r2_lattice3(A_113,B_114,C_115)
      | ~ m1_subset_1(C_115,u1_struct_0(A_113))
      | ~ l1_orders_2(A_113) ) ),
    inference(resolution,[status(thm)],[c_26,c_193])).

tff(c_16,plain,(
    ! [A_18,D_29,C_26,B_25] :
      ( r1_orders_2(A_18,D_29,C_26)
      | ~ r2_hidden(D_29,B_25)
      | ~ m1_subset_1(D_29,u1_struct_0(A_18))
      | ~ r2_lattice3(A_18,B_25,C_26)
      | ~ m1_subset_1(C_26,u1_struct_0(A_18))
      | ~ l1_orders_2(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_361,plain,(
    ! [A_267,A_266,C_268,B_264,C_265] :
      ( r1_orders_2(A_266,'#skF_3'(A_267,B_264,C_268),C_265)
      | ~ m1_subset_1('#skF_3'(A_267,B_264,C_268),u1_struct_0(A_266))
      | ~ r2_lattice3(A_266,'#skF_6',C_265)
      | ~ m1_subset_1(C_265,u1_struct_0(A_266))
      | ~ l1_orders_2(A_266)
      | ~ r1_tarski(B_264,'#skF_5')
      | r2_lattice3(A_267,B_264,C_268)
      | ~ m1_subset_1(C_268,u1_struct_0(A_267))
      | ~ l1_orders_2(A_267) ) ),
    inference(resolution,[status(thm)],[c_200,c_16])).

tff(c_366,plain,(
    ! [A_271,B_272,C_273,C_274] :
      ( r1_orders_2(A_271,'#skF_3'(A_271,B_272,C_273),C_274)
      | ~ r2_lattice3(A_271,'#skF_6',C_274)
      | ~ m1_subset_1(C_274,u1_struct_0(A_271))
      | ~ r1_tarski(B_272,'#skF_5')
      | r2_lattice3(A_271,B_272,C_273)
      | ~ m1_subset_1(C_273,u1_struct_0(A_271))
      | ~ l1_orders_2(A_271) ) ),
    inference(resolution,[status(thm)],[c_22,c_361])).

tff(c_18,plain,(
    ! [A_18,B_25,C_26] :
      ( ~ r1_orders_2(A_18,'#skF_3'(A_18,B_25,C_26),C_26)
      | r2_lattice3(A_18,B_25,C_26)
      | ~ m1_subset_1(C_26,u1_struct_0(A_18))
      | ~ l1_orders_2(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_377,plain,(
    ! [A_275,C_276,B_277] :
      ( ~ r2_lattice3(A_275,'#skF_6',C_276)
      | ~ r1_tarski(B_277,'#skF_5')
      | r2_lattice3(A_275,B_277,C_276)
      | ~ m1_subset_1(C_276,u1_struct_0(A_275))
      | ~ l1_orders_2(A_275) ) ),
    inference(resolution,[status(thm)],[c_366,c_18])).

tff(c_383,plain,(
    ! [B_277] :
      ( ~ r2_lattice3('#skF_4','#skF_6','#skF_7')
      | ~ r1_tarski(B_277,'#skF_5')
      | r2_lattice3('#skF_4',B_277,'#skF_7')
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_377])).

tff(c_389,plain,(
    ! [B_278] :
      ( ~ r1_tarski(B_278,'#skF_5')
      | r2_lattice3('#skF_4',B_278,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_37,c_383])).

tff(c_32,plain,
    ( r1_lattice3('#skF_4','#skF_6','#skF_7')
    | ~ r2_lattice3('#skF_4','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_47,plain,(
    ~ r2_lattice3('#skF_4','#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_394,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_389,c_47])).

tff(c_401,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_394])).

tff(c_402,plain,(
    r1_lattice3('#skF_4','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_14,plain,(
    ! [A_6,B_13,C_14] :
      ( m1_subset_1('#skF_2'(A_6,B_13,C_14),u1_struct_0(A_6))
      | r1_lattice3(A_6,B_13,C_14)
      | ~ m1_subset_1(C_14,u1_struct_0(A_6))
      | ~ l1_orders_2(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_460,plain,(
    ! [A_300,B_301,C_302] :
      ( r2_hidden('#skF_2'(A_300,B_301,C_302),B_301)
      | r1_lattice3(A_300,B_301,C_302)
      | ~ m1_subset_1(C_302,u1_struct_0(A_300))
      | ~ l1_orders_2(A_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_463,plain,(
    ! [A_300,B_301,C_302,B_2] :
      ( r2_hidden('#skF_2'(A_300,B_301,C_302),B_2)
      | ~ r1_tarski(B_301,B_2)
      | r1_lattice3(A_300,B_301,C_302)
      | ~ m1_subset_1(C_302,u1_struct_0(A_300))
      | ~ l1_orders_2(A_300) ) ),
    inference(resolution,[status(thm)],[c_460,c_2])).

tff(c_508,plain,(
    ! [A_331,C_332,D_333,B_334] :
      ( r1_orders_2(A_331,C_332,D_333)
      | ~ r2_hidden(D_333,B_334)
      | ~ m1_subset_1(D_333,u1_struct_0(A_331))
      | ~ r1_lattice3(A_331,B_334,C_332)
      | ~ m1_subset_1(C_332,u1_struct_0(A_331))
      | ~ l1_orders_2(A_331) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_811,plain,(
    ! [C_524,A_528,B_527,C_526,A_525,B_529] :
      ( r1_orders_2(A_525,C_526,'#skF_2'(A_528,B_527,C_524))
      | ~ m1_subset_1('#skF_2'(A_528,B_527,C_524),u1_struct_0(A_525))
      | ~ r1_lattice3(A_525,B_529,C_526)
      | ~ m1_subset_1(C_526,u1_struct_0(A_525))
      | ~ l1_orders_2(A_525)
      | ~ r1_tarski(B_527,B_529)
      | r1_lattice3(A_528,B_527,C_524)
      | ~ m1_subset_1(C_524,u1_struct_0(A_528))
      | ~ l1_orders_2(A_528) ) ),
    inference(resolution,[status(thm)],[c_463,c_508])).

tff(c_833,plain,(
    ! [C_546,B_549,C_547,A_548,B_545] :
      ( r1_orders_2(A_548,C_546,'#skF_2'(A_548,B_545,C_547))
      | ~ r1_lattice3(A_548,B_549,C_546)
      | ~ m1_subset_1(C_546,u1_struct_0(A_548))
      | ~ r1_tarski(B_545,B_549)
      | r1_lattice3(A_548,B_545,C_547)
      | ~ m1_subset_1(C_547,u1_struct_0(A_548))
      | ~ l1_orders_2(A_548) ) ),
    inference(resolution,[status(thm)],[c_14,c_811])).

tff(c_835,plain,(
    ! [B_545,C_547] :
      ( r1_orders_2('#skF_4','#skF_7','#skF_2'('#skF_4',B_545,C_547))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_4'))
      | ~ r1_tarski(B_545,'#skF_6')
      | r1_lattice3('#skF_4',B_545,C_547)
      | ~ m1_subset_1(C_547,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_402,c_833])).

tff(c_839,plain,(
    ! [B_550,C_551] :
      ( r1_orders_2('#skF_4','#skF_7','#skF_2'('#skF_4',B_550,C_551))
      | ~ r1_tarski(B_550,'#skF_6')
      | r1_lattice3('#skF_4',B_550,C_551)
      | ~ m1_subset_1(C_551,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_835])).

tff(c_10,plain,(
    ! [A_6,C_14,B_13] :
      ( ~ r1_orders_2(A_6,C_14,'#skF_2'(A_6,B_13,C_14))
      | r1_lattice3(A_6,B_13,C_14)
      | ~ m1_subset_1(C_14,u1_struct_0(A_6))
      | ~ l1_orders_2(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_843,plain,(
    ! [B_550] :
      ( ~ l1_orders_2('#skF_4')
      | ~ r1_tarski(B_550,'#skF_6')
      | r1_lattice3('#skF_4',B_550,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_839,c_10])).

tff(c_847,plain,(
    ! [B_552] :
      ( ~ r1_tarski(B_552,'#skF_6')
      | r1_lattice3('#skF_4',B_552,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28,c_843])).

tff(c_403,plain,(
    r2_lattice3('#skF_4','#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_30,plain,
    ( ~ r1_lattice3('#skF_4','#skF_5','#skF_7')
    | ~ r2_lattice3('#skF_4','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_405,plain,(
    ~ r1_lattice3('#skF_4','#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_403,c_30])).

tff(c_854,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_847,c_405])).

tff(c_864,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_854])).

tff(c_865,plain,(
    r1_lattice3('#skF_4','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_906,plain,(
    ! [A_570,B_571,C_572] :
      ( r2_hidden('#skF_2'(A_570,B_571,C_572),B_571)
      | r1_lattice3(A_570,B_571,C_572)
      | ~ m1_subset_1(C_572,u1_struct_0(A_570))
      | ~ l1_orders_2(A_570) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_965,plain,(
    ! [A_602,B_603,C_604,B_605] :
      ( r2_hidden('#skF_2'(A_602,B_603,C_604),B_605)
      | ~ r1_tarski(B_603,B_605)
      | r1_lattice3(A_602,B_603,C_604)
      | ~ m1_subset_1(C_604,u1_struct_0(A_602))
      | ~ l1_orders_2(A_602) ) ),
    inference(resolution,[status(thm)],[c_906,c_2])).

tff(c_1005,plain,(
    ! [B_620,C_622,B_621,B_618,A_619] :
      ( r2_hidden('#skF_2'(A_619,B_620,C_622),B_621)
      | ~ r1_tarski(B_618,B_621)
      | ~ r1_tarski(B_620,B_618)
      | r1_lattice3(A_619,B_620,C_622)
      | ~ m1_subset_1(C_622,u1_struct_0(A_619))
      | ~ l1_orders_2(A_619) ) ),
    inference(resolution,[status(thm)],[c_965,c_2])).

tff(c_1012,plain,(
    ! [A_623,B_624,C_625] :
      ( r2_hidden('#skF_2'(A_623,B_624,C_625),'#skF_6')
      | ~ r1_tarski(B_624,'#skF_5')
      | r1_lattice3(A_623,B_624,C_625)
      | ~ m1_subset_1(C_625,u1_struct_0(A_623))
      | ~ l1_orders_2(A_623) ) ),
    inference(resolution,[status(thm)],[c_26,c_1005])).

tff(c_8,plain,(
    ! [A_6,C_14,D_17,B_13] :
      ( r1_orders_2(A_6,C_14,D_17)
      | ~ r2_hidden(D_17,B_13)
      | ~ m1_subset_1(D_17,u1_struct_0(A_6))
      | ~ r1_lattice3(A_6,B_13,C_14)
      | ~ m1_subset_1(C_14,u1_struct_0(A_6))
      | ~ l1_orders_2(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1163,plain,(
    ! [B_747,C_746,C_748,A_750,A_749] :
      ( r1_orders_2(A_749,C_748,'#skF_2'(A_750,B_747,C_746))
      | ~ m1_subset_1('#skF_2'(A_750,B_747,C_746),u1_struct_0(A_749))
      | ~ r1_lattice3(A_749,'#skF_6',C_748)
      | ~ m1_subset_1(C_748,u1_struct_0(A_749))
      | ~ l1_orders_2(A_749)
      | ~ r1_tarski(B_747,'#skF_5')
      | r1_lattice3(A_750,B_747,C_746)
      | ~ m1_subset_1(C_746,u1_struct_0(A_750))
      | ~ l1_orders_2(A_750) ) ),
    inference(resolution,[status(thm)],[c_1012,c_8])).

tff(c_1168,plain,(
    ! [A_756,C_757,B_758,C_759] :
      ( r1_orders_2(A_756,C_757,'#skF_2'(A_756,B_758,C_759))
      | ~ r1_lattice3(A_756,'#skF_6',C_757)
      | ~ m1_subset_1(C_757,u1_struct_0(A_756))
      | ~ r1_tarski(B_758,'#skF_5')
      | r1_lattice3(A_756,B_758,C_759)
      | ~ m1_subset_1(C_759,u1_struct_0(A_756))
      | ~ l1_orders_2(A_756) ) ),
    inference(resolution,[status(thm)],[c_14,c_1163])).

tff(c_1179,plain,(
    ! [A_760,C_761,B_762] :
      ( ~ r1_lattice3(A_760,'#skF_6',C_761)
      | ~ r1_tarski(B_762,'#skF_5')
      | r1_lattice3(A_760,B_762,C_761)
      | ~ m1_subset_1(C_761,u1_struct_0(A_760))
      | ~ l1_orders_2(A_760) ) ),
    inference(resolution,[status(thm)],[c_1168,c_10])).

tff(c_1185,plain,(
    ! [B_762] :
      ( ~ r1_lattice3('#skF_4','#skF_6','#skF_7')
      | ~ r1_tarski(B_762,'#skF_5')
      | r1_lattice3('#skF_4',B_762,'#skF_7')
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_1179])).

tff(c_1191,plain,(
    ! [B_763] :
      ( ~ r1_tarski(B_763,'#skF_5')
      | r1_lattice3('#skF_4',B_763,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_865,c_1185])).

tff(c_866,plain,(
    ~ r2_lattice3('#skF_4','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_34,plain,
    ( ~ r1_lattice3('#skF_4','#skF_5','#skF_7')
    | r2_lattice3('#skF_4','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_875,plain,(
    ~ r1_lattice3('#skF_4','#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_866,c_34])).

tff(c_1194,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_1191,c_875])).

tff(c_1198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_873,c_1194])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:04:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.15/1.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.15/1.72  
% 4.15/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.15/1.72  %$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_tarski > m1_subset_1 > l1_orders_2 > #nlpp > u1_struct_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 4.15/1.72  
% 4.15/1.72  %Foreground sorts:
% 4.15/1.72  
% 4.15/1.72  
% 4.15/1.72  %Background operators:
% 4.15/1.72  
% 4.15/1.72  
% 4.15/1.72  %Foreground operators:
% 4.15/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.15/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.15/1.72  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 4.15/1.72  tff('#skF_7', type, '#skF_7': $i).
% 4.15/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.15/1.72  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 4.15/1.72  tff('#skF_5', type, '#skF_5': $i).
% 4.15/1.72  tff('#skF_6', type, '#skF_6': $i).
% 4.15/1.72  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.15/1.72  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 4.15/1.72  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.15/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.15/1.72  tff('#skF_4', type, '#skF_4': $i).
% 4.15/1.72  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.15/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.15/1.72  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.15/1.72  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.15/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.15/1.72  
% 4.15/1.75  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.15/1.75  tff(f_77, negated_conjecture, ~(![A]: (l1_orders_2(A) => (![B, C]: (r1_tarski(B, C) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r1_lattice3(A, C, D) => r1_lattice3(A, B, D)) & (r2_lattice3(A, C, D) => r2_lattice3(A, B, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_yellow_0)).
% 4.15/1.75  tff(f_60, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, D, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 4.15/1.75  tff(f_46, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattice3)).
% 4.15/1.75  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.15/1.75  tff(c_868, plain, (![A_555, B_556]: (~r2_hidden('#skF_1'(A_555, B_556), B_556) | r1_tarski(A_555, B_556))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.15/1.75  tff(c_873, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_868])).
% 4.15/1.75  tff(c_28, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.15/1.75  tff(c_26, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.15/1.75  tff(c_24, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.15/1.75  tff(c_39, plain, (![A_37, B_38]: (~r2_hidden('#skF_1'(A_37, B_38), B_38) | r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.15/1.75  tff(c_44, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_39])).
% 4.15/1.75  tff(c_36, plain, (r1_lattice3('#skF_4', '#skF_6', '#skF_7') | r2_lattice3('#skF_4', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.15/1.75  tff(c_37, plain, (r2_lattice3('#skF_4', '#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_36])).
% 4.15/1.75  tff(c_22, plain, (![A_18, B_25, C_26]: (m1_subset_1('#skF_3'(A_18, B_25, C_26), u1_struct_0(A_18)) | r2_lattice3(A_18, B_25, C_26) | ~m1_subset_1(C_26, u1_struct_0(A_18)) | ~l1_orders_2(A_18))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.15/1.75  tff(c_68, plain, (![A_50, B_51, C_52]: (r2_hidden('#skF_3'(A_50, B_51, C_52), B_51) | r2_lattice3(A_50, B_51, C_52) | ~m1_subset_1(C_52, u1_struct_0(A_50)) | ~l1_orders_2(A_50))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.15/1.75  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.15/1.75  tff(c_136, plain, (![A_84, B_85, C_86, B_87]: (r2_hidden('#skF_3'(A_84, B_85, C_86), B_87) | ~r1_tarski(B_85, B_87) | r2_lattice3(A_84, B_85, C_86) | ~m1_subset_1(C_86, u1_struct_0(A_84)) | ~l1_orders_2(A_84))), inference(resolution, [status(thm)], [c_68, c_2])).
% 4.15/1.75  tff(c_193, plain, (![B_111, C_108, A_110, B_109, B_112]: (r2_hidden('#skF_3'(A_110, B_111, C_108), B_112) | ~r1_tarski(B_109, B_112) | ~r1_tarski(B_111, B_109) | r2_lattice3(A_110, B_111, C_108) | ~m1_subset_1(C_108, u1_struct_0(A_110)) | ~l1_orders_2(A_110))), inference(resolution, [status(thm)], [c_136, c_2])).
% 4.15/1.75  tff(c_200, plain, (![A_113, B_114, C_115]: (r2_hidden('#skF_3'(A_113, B_114, C_115), '#skF_6') | ~r1_tarski(B_114, '#skF_5') | r2_lattice3(A_113, B_114, C_115) | ~m1_subset_1(C_115, u1_struct_0(A_113)) | ~l1_orders_2(A_113))), inference(resolution, [status(thm)], [c_26, c_193])).
% 4.15/1.75  tff(c_16, plain, (![A_18, D_29, C_26, B_25]: (r1_orders_2(A_18, D_29, C_26) | ~r2_hidden(D_29, B_25) | ~m1_subset_1(D_29, u1_struct_0(A_18)) | ~r2_lattice3(A_18, B_25, C_26) | ~m1_subset_1(C_26, u1_struct_0(A_18)) | ~l1_orders_2(A_18))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.15/1.75  tff(c_361, plain, (![A_267, A_266, C_268, B_264, C_265]: (r1_orders_2(A_266, '#skF_3'(A_267, B_264, C_268), C_265) | ~m1_subset_1('#skF_3'(A_267, B_264, C_268), u1_struct_0(A_266)) | ~r2_lattice3(A_266, '#skF_6', C_265) | ~m1_subset_1(C_265, u1_struct_0(A_266)) | ~l1_orders_2(A_266) | ~r1_tarski(B_264, '#skF_5') | r2_lattice3(A_267, B_264, C_268) | ~m1_subset_1(C_268, u1_struct_0(A_267)) | ~l1_orders_2(A_267))), inference(resolution, [status(thm)], [c_200, c_16])).
% 4.15/1.75  tff(c_366, plain, (![A_271, B_272, C_273, C_274]: (r1_orders_2(A_271, '#skF_3'(A_271, B_272, C_273), C_274) | ~r2_lattice3(A_271, '#skF_6', C_274) | ~m1_subset_1(C_274, u1_struct_0(A_271)) | ~r1_tarski(B_272, '#skF_5') | r2_lattice3(A_271, B_272, C_273) | ~m1_subset_1(C_273, u1_struct_0(A_271)) | ~l1_orders_2(A_271))), inference(resolution, [status(thm)], [c_22, c_361])).
% 4.15/1.75  tff(c_18, plain, (![A_18, B_25, C_26]: (~r1_orders_2(A_18, '#skF_3'(A_18, B_25, C_26), C_26) | r2_lattice3(A_18, B_25, C_26) | ~m1_subset_1(C_26, u1_struct_0(A_18)) | ~l1_orders_2(A_18))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.15/1.75  tff(c_377, plain, (![A_275, C_276, B_277]: (~r2_lattice3(A_275, '#skF_6', C_276) | ~r1_tarski(B_277, '#skF_5') | r2_lattice3(A_275, B_277, C_276) | ~m1_subset_1(C_276, u1_struct_0(A_275)) | ~l1_orders_2(A_275))), inference(resolution, [status(thm)], [c_366, c_18])).
% 4.15/1.75  tff(c_383, plain, (![B_277]: (~r2_lattice3('#skF_4', '#skF_6', '#skF_7') | ~r1_tarski(B_277, '#skF_5') | r2_lattice3('#skF_4', B_277, '#skF_7') | ~l1_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_377])).
% 4.15/1.75  tff(c_389, plain, (![B_278]: (~r1_tarski(B_278, '#skF_5') | r2_lattice3('#skF_4', B_278, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_37, c_383])).
% 4.15/1.75  tff(c_32, plain, (r1_lattice3('#skF_4', '#skF_6', '#skF_7') | ~r2_lattice3('#skF_4', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.15/1.75  tff(c_47, plain, (~r2_lattice3('#skF_4', '#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_32])).
% 4.15/1.75  tff(c_394, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_389, c_47])).
% 4.15/1.75  tff(c_401, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_394])).
% 4.15/1.75  tff(c_402, plain, (r1_lattice3('#skF_4', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_32])).
% 4.15/1.75  tff(c_14, plain, (![A_6, B_13, C_14]: (m1_subset_1('#skF_2'(A_6, B_13, C_14), u1_struct_0(A_6)) | r1_lattice3(A_6, B_13, C_14) | ~m1_subset_1(C_14, u1_struct_0(A_6)) | ~l1_orders_2(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.15/1.75  tff(c_460, plain, (![A_300, B_301, C_302]: (r2_hidden('#skF_2'(A_300, B_301, C_302), B_301) | r1_lattice3(A_300, B_301, C_302) | ~m1_subset_1(C_302, u1_struct_0(A_300)) | ~l1_orders_2(A_300))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.15/1.75  tff(c_463, plain, (![A_300, B_301, C_302, B_2]: (r2_hidden('#skF_2'(A_300, B_301, C_302), B_2) | ~r1_tarski(B_301, B_2) | r1_lattice3(A_300, B_301, C_302) | ~m1_subset_1(C_302, u1_struct_0(A_300)) | ~l1_orders_2(A_300))), inference(resolution, [status(thm)], [c_460, c_2])).
% 4.15/1.75  tff(c_508, plain, (![A_331, C_332, D_333, B_334]: (r1_orders_2(A_331, C_332, D_333) | ~r2_hidden(D_333, B_334) | ~m1_subset_1(D_333, u1_struct_0(A_331)) | ~r1_lattice3(A_331, B_334, C_332) | ~m1_subset_1(C_332, u1_struct_0(A_331)) | ~l1_orders_2(A_331))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.15/1.75  tff(c_811, plain, (![C_524, A_528, B_527, C_526, A_525, B_529]: (r1_orders_2(A_525, C_526, '#skF_2'(A_528, B_527, C_524)) | ~m1_subset_1('#skF_2'(A_528, B_527, C_524), u1_struct_0(A_525)) | ~r1_lattice3(A_525, B_529, C_526) | ~m1_subset_1(C_526, u1_struct_0(A_525)) | ~l1_orders_2(A_525) | ~r1_tarski(B_527, B_529) | r1_lattice3(A_528, B_527, C_524) | ~m1_subset_1(C_524, u1_struct_0(A_528)) | ~l1_orders_2(A_528))), inference(resolution, [status(thm)], [c_463, c_508])).
% 4.15/1.75  tff(c_833, plain, (![C_546, B_549, C_547, A_548, B_545]: (r1_orders_2(A_548, C_546, '#skF_2'(A_548, B_545, C_547)) | ~r1_lattice3(A_548, B_549, C_546) | ~m1_subset_1(C_546, u1_struct_0(A_548)) | ~r1_tarski(B_545, B_549) | r1_lattice3(A_548, B_545, C_547) | ~m1_subset_1(C_547, u1_struct_0(A_548)) | ~l1_orders_2(A_548))), inference(resolution, [status(thm)], [c_14, c_811])).
% 4.15/1.75  tff(c_835, plain, (![B_545, C_547]: (r1_orders_2('#skF_4', '#skF_7', '#skF_2'('#skF_4', B_545, C_547)) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_4')) | ~r1_tarski(B_545, '#skF_6') | r1_lattice3('#skF_4', B_545, C_547) | ~m1_subset_1(C_547, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_402, c_833])).
% 4.15/1.75  tff(c_839, plain, (![B_550, C_551]: (r1_orders_2('#skF_4', '#skF_7', '#skF_2'('#skF_4', B_550, C_551)) | ~r1_tarski(B_550, '#skF_6') | r1_lattice3('#skF_4', B_550, C_551) | ~m1_subset_1(C_551, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_835])).
% 4.15/1.75  tff(c_10, plain, (![A_6, C_14, B_13]: (~r1_orders_2(A_6, C_14, '#skF_2'(A_6, B_13, C_14)) | r1_lattice3(A_6, B_13, C_14) | ~m1_subset_1(C_14, u1_struct_0(A_6)) | ~l1_orders_2(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.15/1.75  tff(c_843, plain, (![B_550]: (~l1_orders_2('#skF_4') | ~r1_tarski(B_550, '#skF_6') | r1_lattice3('#skF_4', B_550, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_839, c_10])).
% 4.15/1.75  tff(c_847, plain, (![B_552]: (~r1_tarski(B_552, '#skF_6') | r1_lattice3('#skF_4', B_552, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_28, c_843])).
% 4.15/1.75  tff(c_403, plain, (r2_lattice3('#skF_4', '#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_32])).
% 4.15/1.75  tff(c_30, plain, (~r1_lattice3('#skF_4', '#skF_5', '#skF_7') | ~r2_lattice3('#skF_4', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.15/1.75  tff(c_405, plain, (~r1_lattice3('#skF_4', '#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_403, c_30])).
% 4.15/1.75  tff(c_854, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_847, c_405])).
% 4.15/1.75  tff(c_864, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_854])).
% 4.15/1.75  tff(c_865, plain, (r1_lattice3('#skF_4', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_36])).
% 4.15/1.75  tff(c_906, plain, (![A_570, B_571, C_572]: (r2_hidden('#skF_2'(A_570, B_571, C_572), B_571) | r1_lattice3(A_570, B_571, C_572) | ~m1_subset_1(C_572, u1_struct_0(A_570)) | ~l1_orders_2(A_570))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.15/1.75  tff(c_965, plain, (![A_602, B_603, C_604, B_605]: (r2_hidden('#skF_2'(A_602, B_603, C_604), B_605) | ~r1_tarski(B_603, B_605) | r1_lattice3(A_602, B_603, C_604) | ~m1_subset_1(C_604, u1_struct_0(A_602)) | ~l1_orders_2(A_602))), inference(resolution, [status(thm)], [c_906, c_2])).
% 4.15/1.75  tff(c_1005, plain, (![B_620, C_622, B_621, B_618, A_619]: (r2_hidden('#skF_2'(A_619, B_620, C_622), B_621) | ~r1_tarski(B_618, B_621) | ~r1_tarski(B_620, B_618) | r1_lattice3(A_619, B_620, C_622) | ~m1_subset_1(C_622, u1_struct_0(A_619)) | ~l1_orders_2(A_619))), inference(resolution, [status(thm)], [c_965, c_2])).
% 4.15/1.75  tff(c_1012, plain, (![A_623, B_624, C_625]: (r2_hidden('#skF_2'(A_623, B_624, C_625), '#skF_6') | ~r1_tarski(B_624, '#skF_5') | r1_lattice3(A_623, B_624, C_625) | ~m1_subset_1(C_625, u1_struct_0(A_623)) | ~l1_orders_2(A_623))), inference(resolution, [status(thm)], [c_26, c_1005])).
% 4.15/1.75  tff(c_8, plain, (![A_6, C_14, D_17, B_13]: (r1_orders_2(A_6, C_14, D_17) | ~r2_hidden(D_17, B_13) | ~m1_subset_1(D_17, u1_struct_0(A_6)) | ~r1_lattice3(A_6, B_13, C_14) | ~m1_subset_1(C_14, u1_struct_0(A_6)) | ~l1_orders_2(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.15/1.75  tff(c_1163, plain, (![B_747, C_746, C_748, A_750, A_749]: (r1_orders_2(A_749, C_748, '#skF_2'(A_750, B_747, C_746)) | ~m1_subset_1('#skF_2'(A_750, B_747, C_746), u1_struct_0(A_749)) | ~r1_lattice3(A_749, '#skF_6', C_748) | ~m1_subset_1(C_748, u1_struct_0(A_749)) | ~l1_orders_2(A_749) | ~r1_tarski(B_747, '#skF_5') | r1_lattice3(A_750, B_747, C_746) | ~m1_subset_1(C_746, u1_struct_0(A_750)) | ~l1_orders_2(A_750))), inference(resolution, [status(thm)], [c_1012, c_8])).
% 4.15/1.75  tff(c_1168, plain, (![A_756, C_757, B_758, C_759]: (r1_orders_2(A_756, C_757, '#skF_2'(A_756, B_758, C_759)) | ~r1_lattice3(A_756, '#skF_6', C_757) | ~m1_subset_1(C_757, u1_struct_0(A_756)) | ~r1_tarski(B_758, '#skF_5') | r1_lattice3(A_756, B_758, C_759) | ~m1_subset_1(C_759, u1_struct_0(A_756)) | ~l1_orders_2(A_756))), inference(resolution, [status(thm)], [c_14, c_1163])).
% 4.15/1.75  tff(c_1179, plain, (![A_760, C_761, B_762]: (~r1_lattice3(A_760, '#skF_6', C_761) | ~r1_tarski(B_762, '#skF_5') | r1_lattice3(A_760, B_762, C_761) | ~m1_subset_1(C_761, u1_struct_0(A_760)) | ~l1_orders_2(A_760))), inference(resolution, [status(thm)], [c_1168, c_10])).
% 4.15/1.75  tff(c_1185, plain, (![B_762]: (~r1_lattice3('#skF_4', '#skF_6', '#skF_7') | ~r1_tarski(B_762, '#skF_5') | r1_lattice3('#skF_4', B_762, '#skF_7') | ~l1_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_1179])).
% 4.15/1.75  tff(c_1191, plain, (![B_763]: (~r1_tarski(B_763, '#skF_5') | r1_lattice3('#skF_4', B_763, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_865, c_1185])).
% 4.15/1.75  tff(c_866, plain, (~r2_lattice3('#skF_4', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_36])).
% 4.15/1.75  tff(c_34, plain, (~r1_lattice3('#skF_4', '#skF_5', '#skF_7') | r2_lattice3('#skF_4', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.15/1.75  tff(c_875, plain, (~r1_lattice3('#skF_4', '#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_866, c_34])).
% 4.15/1.75  tff(c_1194, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_1191, c_875])).
% 4.15/1.75  tff(c_1198, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_873, c_1194])).
% 4.15/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.15/1.75  
% 4.15/1.75  Inference rules
% 4.15/1.75  ----------------------
% 4.15/1.75  #Ref     : 0
% 4.15/1.75  #Sup     : 264
% 4.15/1.75  #Fact    : 0
% 4.15/1.75  #Define  : 0
% 4.15/1.75  #Split   : 4
% 4.15/1.75  #Chain   : 0
% 4.15/1.76  #Close   : 0
% 4.15/1.76  
% 4.15/1.76  Ordering : KBO
% 4.15/1.76  
% 4.15/1.76  Simplification rules
% 4.15/1.76  ----------------------
% 4.15/1.76  #Subsume      : 39
% 4.15/1.76  #Demod        : 56
% 4.15/1.76  #Tautology    : 15
% 4.15/1.76  #SimpNegUnit  : 1
% 4.15/1.76  #BackRed      : 0
% 4.15/1.76  
% 4.15/1.76  #Partial instantiations: 0
% 4.15/1.76  #Strategies tried      : 1
% 4.15/1.76  
% 4.15/1.76  Timing (in seconds)
% 4.15/1.76  ----------------------
% 4.15/1.76  Preprocessing        : 0.27
% 4.15/1.76  Parsing              : 0.15
% 4.15/1.76  CNF conversion       : 0.02
% 4.15/1.76  Main loop            : 0.70
% 4.15/1.76  Inferencing          : 0.29
% 4.15/1.76  Reduction            : 0.15
% 4.15/1.76  Demodulation         : 0.09
% 4.15/1.76  BG Simplification    : 0.03
% 4.15/1.76  Subsumption          : 0.19
% 4.15/1.76  Abstraction          : 0.02
% 4.15/1.76  MUC search           : 0.00
% 4.15/1.76  Cooper               : 0.00
% 4.15/1.76  Total                : 1.03
% 4.15/1.76  Index Insertion      : 0.00
% 4.15/1.76  Index Deletion       : 0.00
% 4.15/1.76  Index Matching       : 0.00
% 4.15/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
