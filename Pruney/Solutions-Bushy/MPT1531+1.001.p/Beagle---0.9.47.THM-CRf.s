%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1531+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:00 EST 2020

% Result     : Theorem 4.78s
% Output     : CNFRefutation 4.78s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 394 expanded)
%              Number of leaves         :   26 ( 144 expanded)
%              Depth                    :   12
%              Number of atoms          :  482 (1330 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
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

tff(f_52,axiom,(
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

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_38,axiom,(
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

tff(c_34,plain,
    ( ~ r1_lattice3('#skF_3','#skF_4','#skF_6')
    | ~ r2_lattice3('#skF_3','#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_47,plain,(
    ~ r2_lattice3('#skF_3','#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_32,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_28,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_30,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_981,plain,(
    ! [A_494,B_495,C_496] :
      ( r2_hidden('#skF_2'(A_494,B_495,C_496),B_495)
      | r2_lattice3(A_494,B_495,C_496)
      | ~ m1_subset_1(C_496,u1_struct_0(A_494))
      | ~ l1_orders_2(A_494) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_22,plain,(
    ! [A_27,B_28] :
      ( m1_subset_1(A_27,k1_zfmisc_1(B_28))
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_973,plain,(
    ! [A_488,C_489,B_490] :
      ( m1_subset_1(A_488,C_489)
      | ~ m1_subset_1(B_490,k1_zfmisc_1(C_489))
      | ~ r2_hidden(A_488,B_490) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_976,plain,(
    ! [A_488,B_28,A_27] :
      ( m1_subset_1(A_488,B_28)
      | ~ r2_hidden(A_488,A_27)
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(resolution,[status(thm)],[c_22,c_973])).

tff(c_986,plain,(
    ! [A_494,B_495,C_496,B_28] :
      ( m1_subset_1('#skF_2'(A_494,B_495,C_496),B_28)
      | ~ r1_tarski(B_495,B_28)
      | r2_lattice3(A_494,B_495,C_496)
      | ~ m1_subset_1(C_496,u1_struct_0(A_494))
      | ~ l1_orders_2(A_494) ) ),
    inference(resolution,[status(thm)],[c_981,c_976])).

tff(c_18,plain,(
    ! [A_25,B_26] :
      ( r2_hidden(A_25,B_26)
      | v1_xboole_0(B_26)
      | ~ m1_subset_1(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_965,plain,(
    ! [C_482,B_483,A_484] :
      ( ~ v1_xboole_0(C_482)
      | ~ m1_subset_1(B_483,k1_zfmisc_1(C_482))
      | ~ r2_hidden(A_484,B_483) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_969,plain,(
    ! [B_485,A_486,A_487] :
      ( ~ v1_xboole_0(B_485)
      | ~ r2_hidden(A_486,A_487)
      | ~ r1_tarski(A_487,B_485) ) ),
    inference(resolution,[status(thm)],[c_22,c_965])).

tff(c_988,plain,(
    ! [B_497,B_498,A_499] :
      ( ~ v1_xboole_0(B_497)
      | ~ r1_tarski(B_498,B_497)
      | v1_xboole_0(B_498)
      | ~ m1_subset_1(A_499,B_498) ) ),
    inference(resolution,[status(thm)],[c_18,c_969])).

tff(c_991,plain,(
    ! [A_499] :
      ( ~ v1_xboole_0('#skF_5')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_499,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_988])).

tff(c_992,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_991])).

tff(c_38,plain,
    ( ~ r1_lattice3('#skF_3','#skF_4','#skF_6')
    | r2_lattice3('#skF_3','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_48,plain,(
    ~ r1_lattice3('#skF_3','#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_565,plain,(
    ! [A_305,B_306,C_307] :
      ( r2_hidden('#skF_1'(A_305,B_306,C_307),B_306)
      | r1_lattice3(A_305,B_306,C_307)
      | ~ m1_subset_1(C_307,u1_struct_0(A_305))
      | ~ l1_orders_2(A_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_547,plain,(
    ! [A_293,C_294,B_295] :
      ( m1_subset_1(A_293,C_294)
      | ~ m1_subset_1(B_295,k1_zfmisc_1(C_294))
      | ~ r2_hidden(A_293,B_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_550,plain,(
    ! [A_293,B_28,A_27] :
      ( m1_subset_1(A_293,B_28)
      | ~ r2_hidden(A_293,A_27)
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(resolution,[status(thm)],[c_22,c_547])).

tff(c_570,plain,(
    ! [A_305,B_306,C_307,B_28] :
      ( m1_subset_1('#skF_1'(A_305,B_306,C_307),B_28)
      | ~ r1_tarski(B_306,B_28)
      | r1_lattice3(A_305,B_306,C_307)
      | ~ m1_subset_1(C_307,u1_struct_0(A_305))
      | ~ l1_orders_2(A_305) ) ),
    inference(resolution,[status(thm)],[c_565,c_550])).

tff(c_539,plain,(
    ! [C_287,B_288,A_289] :
      ( ~ v1_xboole_0(C_287)
      | ~ m1_subset_1(B_288,k1_zfmisc_1(C_287))
      | ~ r2_hidden(A_289,B_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_543,plain,(
    ! [B_290,A_291,A_292] :
      ( ~ v1_xboole_0(B_290)
      | ~ r2_hidden(A_291,A_292)
      | ~ r1_tarski(A_292,B_290) ) ),
    inference(resolution,[status(thm)],[c_22,c_539])).

tff(c_555,plain,(
    ! [B_299,B_300,A_301] :
      ( ~ v1_xboole_0(B_299)
      | ~ r1_tarski(B_300,B_299)
      | v1_xboole_0(B_300)
      | ~ m1_subset_1(A_301,B_300) ) ),
    inference(resolution,[status(thm)],[c_18,c_543])).

tff(c_558,plain,(
    ! [A_301] :
      ( ~ v1_xboole_0('#skF_5')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_301,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_555])).

tff(c_559,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_558])).

tff(c_88,plain,(
    ! [A_71,B_72,C_73] :
      ( r2_hidden('#skF_2'(A_71,B_72,C_73),B_72)
      | r2_lattice3(A_71,B_72,C_73)
      | ~ m1_subset_1(C_73,u1_struct_0(A_71))
      | ~ l1_orders_2(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_59,plain,(
    ! [A_52,C_53,B_54] :
      ( m1_subset_1(A_52,C_53)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(C_53))
      | ~ r2_hidden(A_52,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_62,plain,(
    ! [A_52,B_28,A_27] :
      ( m1_subset_1(A_52,B_28)
      | ~ r2_hidden(A_52,A_27)
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(resolution,[status(thm)],[c_22,c_59])).

tff(c_93,plain,(
    ! [A_71,B_72,C_73,B_28] :
      ( m1_subset_1('#skF_2'(A_71,B_72,C_73),B_28)
      | ~ r1_tarski(B_72,B_28)
      | r2_lattice3(A_71,B_72,C_73)
      | ~ m1_subset_1(C_73,u1_struct_0(A_71))
      | ~ l1_orders_2(A_71) ) ),
    inference(resolution,[status(thm)],[c_88,c_62])).

tff(c_51,plain,(
    ! [C_46,B_47,A_48] :
      ( ~ v1_xboole_0(C_46)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(C_46))
      | ~ r2_hidden(A_48,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_55,plain,(
    ! [B_49,A_50,A_51] :
      ( ~ v1_xboole_0(B_49)
      | ~ r2_hidden(A_50,A_51)
      | ~ r1_tarski(A_51,B_49) ) ),
    inference(resolution,[status(thm)],[c_22,c_51])).

tff(c_67,plain,(
    ! [B_58,B_59,A_60] :
      ( ~ v1_xboole_0(B_58)
      | ~ r1_tarski(B_59,B_58)
      | v1_xboole_0(B_59)
      | ~ m1_subset_1(A_60,B_59) ) ),
    inference(resolution,[status(thm)],[c_18,c_55])).

tff(c_70,plain,(
    ! [A_60] :
      ( ~ v1_xboole_0('#skF_5')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_60,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_67])).

tff(c_71,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_40,plain,
    ( r1_lattice3('#skF_3','#skF_5','#skF_6')
    | r2_lattice3('#skF_3','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_49,plain,(
    r2_lattice3('#skF_3','#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_16,plain,(
    ! [A_13,B_20,C_21] :
      ( m1_subset_1('#skF_2'(A_13,B_20,C_21),u1_struct_0(A_13))
      | r2_lattice3(A_13,B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0(A_13))
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_157,plain,(
    ! [A_106,D_107,C_108,B_109] :
      ( r1_orders_2(A_106,D_107,C_108)
      | ~ r2_hidden(D_107,B_109)
      | ~ m1_subset_1(D_107,u1_struct_0(A_106))
      | ~ r2_lattice3(A_106,B_109,C_108)
      | ~ m1_subset_1(C_108,u1_struct_0(A_106))
      | ~ l1_orders_2(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_203,plain,(
    ! [A_124,A_125,C_126,B_127] :
      ( r1_orders_2(A_124,A_125,C_126)
      | ~ m1_subset_1(A_125,u1_struct_0(A_124))
      | ~ r2_lattice3(A_124,B_127,C_126)
      | ~ m1_subset_1(C_126,u1_struct_0(A_124))
      | ~ l1_orders_2(A_124)
      | v1_xboole_0(B_127)
      | ~ m1_subset_1(A_125,B_127) ) ),
    inference(resolution,[status(thm)],[c_18,c_157])).

tff(c_460,plain,(
    ! [C_263,C_266,B_267,A_265,B_264] :
      ( r1_orders_2(A_265,'#skF_2'(A_265,B_264,C_263),C_266)
      | ~ r2_lattice3(A_265,B_267,C_266)
      | ~ m1_subset_1(C_266,u1_struct_0(A_265))
      | v1_xboole_0(B_267)
      | ~ m1_subset_1('#skF_2'(A_265,B_264,C_263),B_267)
      | r2_lattice3(A_265,B_264,C_263)
      | ~ m1_subset_1(C_263,u1_struct_0(A_265))
      | ~ l1_orders_2(A_265) ) ),
    inference(resolution,[status(thm)],[c_16,c_203])).

tff(c_462,plain,(
    ! [B_264,C_263] :
      ( r1_orders_2('#skF_3','#skF_2'('#skF_3',B_264,C_263),'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1('#skF_2'('#skF_3',B_264,C_263),'#skF_5')
      | r2_lattice3('#skF_3',B_264,C_263)
      | ~ m1_subset_1(C_263,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_49,c_460])).

tff(c_465,plain,(
    ! [B_264,C_263] :
      ( r1_orders_2('#skF_3','#skF_2'('#skF_3',B_264,C_263),'#skF_6')
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1('#skF_2'('#skF_3',B_264,C_263),'#skF_5')
      | r2_lattice3('#skF_3',B_264,C_263)
      | ~ m1_subset_1(C_263,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_462])).

tff(c_467,plain,(
    ! [B_268,C_269] :
      ( r1_orders_2('#skF_3','#skF_2'('#skF_3',B_268,C_269),'#skF_6')
      | ~ m1_subset_1('#skF_2'('#skF_3',B_268,C_269),'#skF_5')
      | r2_lattice3('#skF_3',B_268,C_269)
      | ~ m1_subset_1(C_269,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_465])).

tff(c_12,plain,(
    ! [A_13,B_20,C_21] :
      ( ~ r1_orders_2(A_13,'#skF_2'(A_13,B_20,C_21),C_21)
      | r2_lattice3(A_13,B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0(A_13))
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_471,plain,(
    ! [B_268] :
      ( ~ l1_orders_2('#skF_3')
      | ~ m1_subset_1('#skF_2'('#skF_3',B_268,'#skF_6'),'#skF_5')
      | r2_lattice3('#skF_3',B_268,'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_467,c_12])).

tff(c_475,plain,(
    ! [B_270] :
      ( ~ m1_subset_1('#skF_2'('#skF_3',B_270,'#skF_6'),'#skF_5')
      | r2_lattice3('#skF_3',B_270,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_471])).

tff(c_479,plain,(
    ! [B_72] :
      ( ~ r1_tarski(B_72,'#skF_5')
      | r2_lattice3('#skF_3',B_72,'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_93,c_475])).

tff(c_483,plain,(
    ! [B_271] :
      ( ~ r1_tarski(B_271,'#skF_5')
      | r2_lattice3('#skF_3',B_271,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_479])).

tff(c_492,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_483,c_47])).

tff(c_505,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_492])).

tff(c_507,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_509,plain,(
    ! [A_272,B_273,C_274] :
      ( r2_hidden('#skF_1'(A_272,B_273,C_274),B_273)
      | r1_lattice3(A_272,B_273,C_274)
      | ~ m1_subset_1(C_274,u1_struct_0(A_272))
      | ~ l1_orders_2(A_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_54,plain,(
    ! [B_28,A_48,A_27] :
      ( ~ v1_xboole_0(B_28)
      | ~ r2_hidden(A_48,A_27)
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(resolution,[status(thm)],[c_22,c_51])).

tff(c_521,plain,(
    ! [B_279,B_280,A_281,C_282] :
      ( ~ v1_xboole_0(B_279)
      | ~ r1_tarski(B_280,B_279)
      | r1_lattice3(A_281,B_280,C_282)
      | ~ m1_subset_1(C_282,u1_struct_0(A_281))
      | ~ l1_orders_2(A_281) ) ),
    inference(resolution,[status(thm)],[c_509,c_54])).

tff(c_523,plain,(
    ! [A_281,C_282] :
      ( ~ v1_xboole_0('#skF_5')
      | r1_lattice3(A_281,'#skF_4',C_282)
      | ~ m1_subset_1(C_282,u1_struct_0(A_281))
      | ~ l1_orders_2(A_281) ) ),
    inference(resolution,[status(thm)],[c_30,c_521])).

tff(c_527,plain,(
    ! [A_283,C_284] :
      ( r1_lattice3(A_283,'#skF_4',C_284)
      | ~ m1_subset_1(C_284,u1_struct_0(A_283))
      | ~ l1_orders_2(A_283) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_507,c_523])).

tff(c_530,plain,
    ( r1_lattice3('#skF_3','#skF_4','#skF_6')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_527])).

tff(c_533,plain,(
    r1_lattice3('#skF_3','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_530])).

tff(c_535,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_533])).

tff(c_536,plain,(
    r1_lattice3('#skF_3','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_8,plain,(
    ! [A_1,B_8,C_9] :
      ( m1_subset_1('#skF_1'(A_1,B_8,C_9),u1_struct_0(A_1))
      | r1_lattice3(A_1,B_8,C_9)
      | ~ m1_subset_1(C_9,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_655,plain,(
    ! [A_351,C_352,D_353,B_354] :
      ( r1_orders_2(A_351,C_352,D_353)
      | ~ r2_hidden(D_353,B_354)
      | ~ m1_subset_1(D_353,u1_struct_0(A_351))
      | ~ r1_lattice3(A_351,B_354,C_352)
      | ~ m1_subset_1(C_352,u1_struct_0(A_351))
      | ~ l1_orders_2(A_351) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_712,plain,(
    ! [A_371,C_372,A_373,B_374] :
      ( r1_orders_2(A_371,C_372,A_373)
      | ~ m1_subset_1(A_373,u1_struct_0(A_371))
      | ~ r1_lattice3(A_371,B_374,C_372)
      | ~ m1_subset_1(C_372,u1_struct_0(A_371))
      | ~ l1_orders_2(A_371)
      | v1_xboole_0(B_374)
      | ~ m1_subset_1(A_373,B_374) ) ),
    inference(resolution,[status(thm)],[c_18,c_655])).

tff(c_890,plain,(
    ! [B_462,C_460,A_461,B_458,C_459] :
      ( r1_orders_2(A_461,C_459,'#skF_1'(A_461,B_458,C_460))
      | ~ r1_lattice3(A_461,B_462,C_459)
      | ~ m1_subset_1(C_459,u1_struct_0(A_461))
      | v1_xboole_0(B_462)
      | ~ m1_subset_1('#skF_1'(A_461,B_458,C_460),B_462)
      | r1_lattice3(A_461,B_458,C_460)
      | ~ m1_subset_1(C_460,u1_struct_0(A_461))
      | ~ l1_orders_2(A_461) ) ),
    inference(resolution,[status(thm)],[c_8,c_712])).

tff(c_892,plain,(
    ! [B_458,C_460] :
      ( r1_orders_2('#skF_3','#skF_6','#skF_1'('#skF_3',B_458,C_460))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_458,C_460),'#skF_5')
      | r1_lattice3('#skF_3',B_458,C_460)
      | ~ m1_subset_1(C_460,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_536,c_890])).

tff(c_895,plain,(
    ! [B_458,C_460] :
      ( r1_orders_2('#skF_3','#skF_6','#skF_1'('#skF_3',B_458,C_460))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_458,C_460),'#skF_5')
      | r1_lattice3('#skF_3',B_458,C_460)
      | ~ m1_subset_1(C_460,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_892])).

tff(c_897,plain,(
    ! [B_463,C_464] :
      ( r1_orders_2('#skF_3','#skF_6','#skF_1'('#skF_3',B_463,C_464))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_463,C_464),'#skF_5')
      | r1_lattice3('#skF_3',B_463,C_464)
      | ~ m1_subset_1(C_464,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_559,c_895])).

tff(c_4,plain,(
    ! [A_1,C_9,B_8] :
      ( ~ r1_orders_2(A_1,C_9,'#skF_1'(A_1,B_8,C_9))
      | r1_lattice3(A_1,B_8,C_9)
      | ~ m1_subset_1(C_9,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_901,plain,(
    ! [B_463] :
      ( ~ l1_orders_2('#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_463,'#skF_6'),'#skF_5')
      | r1_lattice3('#skF_3',B_463,'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_897,c_4])).

tff(c_905,plain,(
    ! [B_465] :
      ( ~ m1_subset_1('#skF_1'('#skF_3',B_465,'#skF_6'),'#skF_5')
      | r1_lattice3('#skF_3',B_465,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_901])).

tff(c_909,plain,(
    ! [B_306] :
      ( ~ r1_tarski(B_306,'#skF_5')
      | r1_lattice3('#skF_3',B_306,'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_570,c_905])).

tff(c_913,plain,(
    ! [B_466] :
      ( ~ r1_tarski(B_466,'#skF_5')
      | r1_lattice3('#skF_3',B_466,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_909])).

tff(c_920,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_913,c_48])).

tff(c_930,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_920])).

tff(c_932,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_558])).

tff(c_934,plain,(
    ! [A_467,B_468,C_469] :
      ( r2_hidden('#skF_1'(A_467,B_468,C_469),B_468)
      | r1_lattice3(A_467,B_468,C_469)
      | ~ m1_subset_1(C_469,u1_struct_0(A_467))
      | ~ l1_orders_2(A_467) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_542,plain,(
    ! [B_28,A_289,A_27] :
      ( ~ v1_xboole_0(B_28)
      | ~ r2_hidden(A_289,A_27)
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(resolution,[status(thm)],[c_22,c_539])).

tff(c_946,plain,(
    ! [B_474,B_475,A_476,C_477] :
      ( ~ v1_xboole_0(B_474)
      | ~ r1_tarski(B_475,B_474)
      | r1_lattice3(A_476,B_475,C_477)
      | ~ m1_subset_1(C_477,u1_struct_0(A_476))
      | ~ l1_orders_2(A_476) ) ),
    inference(resolution,[status(thm)],[c_934,c_542])).

tff(c_948,plain,(
    ! [A_476,C_477] :
      ( ~ v1_xboole_0('#skF_5')
      | r1_lattice3(A_476,'#skF_4',C_477)
      | ~ m1_subset_1(C_477,u1_struct_0(A_476))
      | ~ l1_orders_2(A_476) ) ),
    inference(resolution,[status(thm)],[c_30,c_946])).

tff(c_952,plain,(
    ! [A_478,C_479] :
      ( r1_lattice3(A_478,'#skF_4',C_479)
      | ~ m1_subset_1(C_479,u1_struct_0(A_478))
      | ~ l1_orders_2(A_478) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_932,c_948])).

tff(c_955,plain,
    ( r1_lattice3('#skF_3','#skF_4','#skF_6')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_952])).

tff(c_958,plain,(
    r1_lattice3('#skF_3','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_955])).

tff(c_960,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_958])).

tff(c_961,plain,(
    r2_lattice3('#skF_3','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_1045,plain,(
    ! [A_534,D_535,C_536,B_537] :
      ( r1_orders_2(A_534,D_535,C_536)
      | ~ r2_hidden(D_535,B_537)
      | ~ m1_subset_1(D_535,u1_struct_0(A_534))
      | ~ r2_lattice3(A_534,B_537,C_536)
      | ~ m1_subset_1(C_536,u1_struct_0(A_534))
      | ~ l1_orders_2(A_534) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1117,plain,(
    ! [A_560,A_561,C_562,B_563] :
      ( r1_orders_2(A_560,A_561,C_562)
      | ~ m1_subset_1(A_561,u1_struct_0(A_560))
      | ~ r2_lattice3(A_560,B_563,C_562)
      | ~ m1_subset_1(C_562,u1_struct_0(A_560))
      | ~ l1_orders_2(A_560)
      | v1_xboole_0(B_563)
      | ~ m1_subset_1(A_561,B_563) ) ),
    inference(resolution,[status(thm)],[c_18,c_1045])).

tff(c_1359,plain,(
    ! [C_685,A_689,B_688,B_687,C_686] :
      ( r1_orders_2(A_689,'#skF_2'(A_689,B_687,C_686),C_685)
      | ~ r2_lattice3(A_689,B_688,C_685)
      | ~ m1_subset_1(C_685,u1_struct_0(A_689))
      | v1_xboole_0(B_688)
      | ~ m1_subset_1('#skF_2'(A_689,B_687,C_686),B_688)
      | r2_lattice3(A_689,B_687,C_686)
      | ~ m1_subset_1(C_686,u1_struct_0(A_689))
      | ~ l1_orders_2(A_689) ) ),
    inference(resolution,[status(thm)],[c_16,c_1117])).

tff(c_1361,plain,(
    ! [B_687,C_686] :
      ( r1_orders_2('#skF_3','#skF_2'('#skF_3',B_687,C_686),'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1('#skF_2'('#skF_3',B_687,C_686),'#skF_5')
      | r2_lattice3('#skF_3',B_687,C_686)
      | ~ m1_subset_1(C_686,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_961,c_1359])).

tff(c_1364,plain,(
    ! [B_687,C_686] :
      ( r1_orders_2('#skF_3','#skF_2'('#skF_3',B_687,C_686),'#skF_6')
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1('#skF_2'('#skF_3',B_687,C_686),'#skF_5')
      | r2_lattice3('#skF_3',B_687,C_686)
      | ~ m1_subset_1(C_686,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_1361])).

tff(c_1366,plain,(
    ! [B_690,C_691] :
      ( r1_orders_2('#skF_3','#skF_2'('#skF_3',B_690,C_691),'#skF_6')
      | ~ m1_subset_1('#skF_2'('#skF_3',B_690,C_691),'#skF_5')
      | r2_lattice3('#skF_3',B_690,C_691)
      | ~ m1_subset_1(C_691,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_992,c_1364])).

tff(c_1370,plain,(
    ! [B_690] :
      ( ~ l1_orders_2('#skF_3')
      | ~ m1_subset_1('#skF_2'('#skF_3',B_690,'#skF_6'),'#skF_5')
      | r2_lattice3('#skF_3',B_690,'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1366,c_12])).

tff(c_1374,plain,(
    ! [B_692] :
      ( ~ m1_subset_1('#skF_2'('#skF_3',B_692,'#skF_6'),'#skF_5')
      | r2_lattice3('#skF_3',B_692,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_1370])).

tff(c_1378,plain,(
    ! [B_495] :
      ( ~ r1_tarski(B_495,'#skF_5')
      | r2_lattice3('#skF_3',B_495,'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_986,c_1374])).

tff(c_1382,plain,(
    ! [B_693] :
      ( ~ r1_tarski(B_693,'#skF_5')
      | r2_lattice3('#skF_3',B_693,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_1378])).

tff(c_1391,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_1382,c_47])).

tff(c_1404,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1391])).

tff(c_1406,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_991])).

tff(c_968,plain,(
    ! [B_28,A_484,A_27] :
      ( ~ v1_xboole_0(B_28)
      | ~ r2_hidden(A_484,A_27)
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(resolution,[status(thm)],[c_22,c_965])).

tff(c_1420,plain,(
    ! [B_701,B_702,A_703,C_704] :
      ( ~ v1_xboole_0(B_701)
      | ~ r1_tarski(B_702,B_701)
      | r2_lattice3(A_703,B_702,C_704)
      | ~ m1_subset_1(C_704,u1_struct_0(A_703))
      | ~ l1_orders_2(A_703) ) ),
    inference(resolution,[status(thm)],[c_981,c_968])).

tff(c_1422,plain,(
    ! [A_703,C_704] :
      ( ~ v1_xboole_0('#skF_5')
      | r2_lattice3(A_703,'#skF_4',C_704)
      | ~ m1_subset_1(C_704,u1_struct_0(A_703))
      | ~ l1_orders_2(A_703) ) ),
    inference(resolution,[status(thm)],[c_30,c_1420])).

tff(c_1426,plain,(
    ! [A_705,C_706] :
      ( r2_lattice3(A_705,'#skF_4',C_706)
      | ~ m1_subset_1(C_706,u1_struct_0(A_705))
      | ~ l1_orders_2(A_705) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1406,c_1422])).

tff(c_1429,plain,
    ( r2_lattice3('#skF_3','#skF_4','#skF_6')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_1426])).

tff(c_1432,plain,(
    r2_lattice3('#skF_3','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1429])).

tff(c_1434,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_1432])).

tff(c_1435,plain,(
    ~ r1_lattice3('#skF_3','#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_1479,plain,(
    ! [A_734,B_735,C_736] :
      ( r2_hidden('#skF_1'(A_734,B_735,C_736),B_735)
      | r1_lattice3(A_734,B_735,C_736)
      | ~ m1_subset_1(C_736,u1_struct_0(A_734))
      | ~ l1_orders_2(A_734) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1450,plain,(
    ! [A_715,C_716,B_717] :
      ( m1_subset_1(A_715,C_716)
      | ~ m1_subset_1(B_717,k1_zfmisc_1(C_716))
      | ~ r2_hidden(A_715,B_717) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1453,plain,(
    ! [A_715,B_28,A_27] :
      ( m1_subset_1(A_715,B_28)
      | ~ r2_hidden(A_715,A_27)
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(resolution,[status(thm)],[c_22,c_1450])).

tff(c_1484,plain,(
    ! [A_734,B_735,C_736,B_28] :
      ( m1_subset_1('#skF_1'(A_734,B_735,C_736),B_28)
      | ~ r1_tarski(B_735,B_28)
      | r1_lattice3(A_734,B_735,C_736)
      | ~ m1_subset_1(C_736,u1_struct_0(A_734))
      | ~ l1_orders_2(A_734) ) ),
    inference(resolution,[status(thm)],[c_1479,c_1453])).

tff(c_1442,plain,(
    ! [C_709,B_710,A_711] :
      ( ~ v1_xboole_0(C_709)
      | ~ m1_subset_1(B_710,k1_zfmisc_1(C_709))
      | ~ r2_hidden(A_711,B_710) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1446,plain,(
    ! [B_712,A_713,A_714] :
      ( ~ v1_xboole_0(B_712)
      | ~ r2_hidden(A_713,A_714)
      | ~ r1_tarski(A_714,B_712) ) ),
    inference(resolution,[status(thm)],[c_22,c_1442])).

tff(c_1458,plain,(
    ! [B_721,B_722,A_723] :
      ( ~ v1_xboole_0(B_721)
      | ~ r1_tarski(B_722,B_721)
      | v1_xboole_0(B_722)
      | ~ m1_subset_1(A_723,B_722) ) ),
    inference(resolution,[status(thm)],[c_18,c_1446])).

tff(c_1461,plain,(
    ! [A_723] :
      ( ~ v1_xboole_0('#skF_5')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_723,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_1458])).

tff(c_1462,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1461])).

tff(c_1436,plain,(
    r2_lattice3('#skF_3','#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_36,plain,
    ( r1_lattice3('#skF_3','#skF_5','#skF_6')
    | ~ r2_lattice3('#skF_3','#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1441,plain,(
    r1_lattice3('#skF_3','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1436,c_36])).

tff(c_1545,plain,(
    ! [A_769,C_770,D_771,B_772] :
      ( r1_orders_2(A_769,C_770,D_771)
      | ~ r2_hidden(D_771,B_772)
      | ~ m1_subset_1(D_771,u1_struct_0(A_769))
      | ~ r1_lattice3(A_769,B_772,C_770)
      | ~ m1_subset_1(C_770,u1_struct_0(A_769))
      | ~ l1_orders_2(A_769) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1626,plain,(
    ! [A_793,C_794,A_795,B_796] :
      ( r1_orders_2(A_793,C_794,A_795)
      | ~ m1_subset_1(A_795,u1_struct_0(A_793))
      | ~ r1_lattice3(A_793,B_796,C_794)
      | ~ m1_subset_1(C_794,u1_struct_0(A_793))
      | ~ l1_orders_2(A_793)
      | v1_xboole_0(B_796)
      | ~ m1_subset_1(A_795,B_796) ) ),
    inference(resolution,[status(thm)],[c_18,c_1545])).

tff(c_1840,plain,(
    ! [C_902,A_906,B_903,B_905,C_904] :
      ( r1_orders_2(A_906,C_902,'#skF_1'(A_906,B_903,C_904))
      | ~ r1_lattice3(A_906,B_905,C_902)
      | ~ m1_subset_1(C_902,u1_struct_0(A_906))
      | v1_xboole_0(B_905)
      | ~ m1_subset_1('#skF_1'(A_906,B_903,C_904),B_905)
      | r1_lattice3(A_906,B_903,C_904)
      | ~ m1_subset_1(C_904,u1_struct_0(A_906))
      | ~ l1_orders_2(A_906) ) ),
    inference(resolution,[status(thm)],[c_8,c_1626])).

tff(c_1842,plain,(
    ! [B_903,C_904] :
      ( r1_orders_2('#skF_3','#skF_6','#skF_1'('#skF_3',B_903,C_904))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_903,C_904),'#skF_5')
      | r1_lattice3('#skF_3',B_903,C_904)
      | ~ m1_subset_1(C_904,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1441,c_1840])).

tff(c_1845,plain,(
    ! [B_903,C_904] :
      ( r1_orders_2('#skF_3','#skF_6','#skF_1'('#skF_3',B_903,C_904))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_903,C_904),'#skF_5')
      | r1_lattice3('#skF_3',B_903,C_904)
      | ~ m1_subset_1(C_904,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_1842])).

tff(c_1847,plain,(
    ! [B_907,C_908] :
      ( r1_orders_2('#skF_3','#skF_6','#skF_1'('#skF_3',B_907,C_908))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_907,C_908),'#skF_5')
      | r1_lattice3('#skF_3',B_907,C_908)
      | ~ m1_subset_1(C_908,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1462,c_1845])).

tff(c_1851,plain,(
    ! [B_907] :
      ( ~ l1_orders_2('#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_907,'#skF_6'),'#skF_5')
      | r1_lattice3('#skF_3',B_907,'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1847,c_4])).

tff(c_1855,plain,(
    ! [B_909] :
      ( ~ m1_subset_1('#skF_1'('#skF_3',B_909,'#skF_6'),'#skF_5')
      | r1_lattice3('#skF_3',B_909,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_1851])).

tff(c_1859,plain,(
    ! [B_735] :
      ( ~ r1_tarski(B_735,'#skF_5')
      | r1_lattice3('#skF_3',B_735,'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1484,c_1855])).

tff(c_1863,plain,(
    ! [B_910] :
      ( ~ r1_tarski(B_910,'#skF_5')
      | r1_lattice3('#skF_3',B_910,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_1859])).

tff(c_1872,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_1863,c_1435])).

tff(c_1885,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1872])).

tff(c_1887,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1461])).

tff(c_1890,plain,(
    ! [A_912,B_913,C_914] :
      ( r2_hidden('#skF_1'(A_912,B_913,C_914),B_913)
      | r1_lattice3(A_912,B_913,C_914)
      | ~ m1_subset_1(C_914,u1_struct_0(A_912))
      | ~ l1_orders_2(A_912) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1445,plain,(
    ! [B_28,A_711,A_27] :
      ( ~ v1_xboole_0(B_28)
      | ~ r2_hidden(A_711,A_27)
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(resolution,[status(thm)],[c_22,c_1442])).

tff(c_1901,plain,(
    ! [B_918,B_919,A_920,C_921] :
      ( ~ v1_xboole_0(B_918)
      | ~ r1_tarski(B_919,B_918)
      | r1_lattice3(A_920,B_919,C_921)
      | ~ m1_subset_1(C_921,u1_struct_0(A_920))
      | ~ l1_orders_2(A_920) ) ),
    inference(resolution,[status(thm)],[c_1890,c_1445])).

tff(c_1903,plain,(
    ! [A_920,C_921] :
      ( ~ v1_xboole_0('#skF_5')
      | r1_lattice3(A_920,'#skF_4',C_921)
      | ~ m1_subset_1(C_921,u1_struct_0(A_920))
      | ~ l1_orders_2(A_920) ) ),
    inference(resolution,[status(thm)],[c_30,c_1901])).

tff(c_1907,plain,(
    ! [A_922,C_923] :
      ( r1_lattice3(A_922,'#skF_4',C_923)
      | ~ m1_subset_1(C_923,u1_struct_0(A_922))
      | ~ l1_orders_2(A_922) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1887,c_1903])).

tff(c_1910,plain,
    ( r1_lattice3('#skF_3','#skF_4','#skF_6')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_1907])).

tff(c_1913,plain,(
    r1_lattice3('#skF_3','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1910])).

tff(c_1915,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1435,c_1913])).

%------------------------------------------------------------------------------
