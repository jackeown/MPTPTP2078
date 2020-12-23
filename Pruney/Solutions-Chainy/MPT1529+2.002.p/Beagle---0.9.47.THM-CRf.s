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
% DateTime   : Thu Dec  3 10:24:58 EST 2020

% Result     : Theorem 10.30s
% Output     : CNFRefutation 10.49s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 310 expanded)
%              Number of leaves         :   24 ( 110 expanded)
%              Depth                    :   10
%              Number of atoms          :  233 (1272 expanded)
%              Number of equality atoms :   21 (  68 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > m1_subset_1 > l1_orders_2 > k2_tarski > #nlpp > u1_struct_0 > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( ( r1_lattice3(A,k1_tarski(C),B)
                   => r1_orders_2(A,B,C) )
                  & ( r1_orders_2(A,B,C)
                   => r1_lattice3(A,k1_tarski(C),B) )
                  & ( r2_lattice3(A,k1_tarski(C),B)
                   => r1_orders_2(A,C,B) )
                  & ( r1_orders_2(A,C,B)
                   => r2_lattice3(A,k1_tarski(C),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_yellow_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).

tff(c_44,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ r1_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6')
    | ~ r1_orders_2('#skF_5','#skF_7','#skF_6')
    | ~ r2_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_108,plain,(
    ~ r2_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_42,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_68,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ r1_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6')
    | r2_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6')
    | r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_142,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ r1_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6')
    | r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_68])).

tff(c_143,plain,(
    ~ r1_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_74,plain,
    ( r1_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6')
    | r1_orders_2('#skF_5','#skF_6','#skF_7')
    | r2_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6')
    | r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_175,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_7')
    | r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_143,c_74])).

tff(c_176,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_175])).

tff(c_117,plain,(
    ! [A_53,B_54,C_55] :
      ( r2_hidden('#skF_4'(A_53,B_54,C_55),B_54)
      | r2_lattice3(A_53,B_54,C_55)
      | ~ m1_subset_1(C_55,u1_struct_0(A_53))
      | ~ l1_orders_2(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_94,plain,(
    ! [D_42,B_43,A_44] :
      ( D_42 = B_43
      | D_42 = A_44
      | ~ r2_hidden(D_42,k2_tarski(A_44,B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_103,plain,(
    ! [D_42,A_7] :
      ( D_42 = A_7
      | D_42 = A_7
      | ~ r2_hidden(D_42,k1_tarski(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_94])).

tff(c_177,plain,(
    ! [A_77,A_78,C_79] :
      ( '#skF_4'(A_77,k1_tarski(A_78),C_79) = A_78
      | r2_lattice3(A_77,k1_tarski(A_78),C_79)
      | ~ m1_subset_1(C_79,u1_struct_0(A_77))
      | ~ l1_orders_2(A_77) ) ),
    inference(resolution,[status(thm)],[c_117,c_103])).

tff(c_180,plain,
    ( '#skF_4'('#skF_5',k1_tarski('#skF_7'),'#skF_6') = '#skF_7'
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_177,c_108])).

tff(c_183,plain,(
    '#skF_4'('#skF_5',k1_tarski('#skF_7'),'#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_180])).

tff(c_32,plain,(
    ! [A_20,B_27,C_28] :
      ( ~ r1_orders_2(A_20,'#skF_4'(A_20,B_27,C_28),C_28)
      | r2_lattice3(A_20,B_27,C_28)
      | ~ m1_subset_1(C_28,u1_struct_0(A_20))
      | ~ l1_orders_2(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_193,plain,
    ( ~ r1_orders_2('#skF_5','#skF_7','#skF_6')
    | r2_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_32])).

tff(c_203,plain,(
    r2_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_176,c_193])).

tff(c_205,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_203])).

tff(c_206,plain,(
    r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_175])).

tff(c_129,plain,(
    ! [A_59,B_60,C_61] :
      ( r2_hidden('#skF_3'(A_59,B_60,C_61),B_60)
      | r1_lattice3(A_59,B_60,C_61)
      | ~ m1_subset_1(C_61,u1_struct_0(A_59))
      | ~ l1_orders_2(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_146,plain,(
    ! [A_74,A_75,C_76] :
      ( '#skF_3'(A_74,k1_tarski(A_75),C_76) = A_75
      | r1_lattice3(A_74,k1_tarski(A_75),C_76)
      | ~ m1_subset_1(C_76,u1_struct_0(A_74))
      | ~ l1_orders_2(A_74) ) ),
    inference(resolution,[status(thm)],[c_129,c_103])).

tff(c_149,plain,
    ( '#skF_3'('#skF_5',k1_tarski('#skF_7'),'#skF_6') = '#skF_7'
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_146,c_143])).

tff(c_152,plain,(
    '#skF_3'('#skF_5',k1_tarski('#skF_7'),'#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_149])).

tff(c_24,plain,(
    ! [A_8,C_16,B_15] :
      ( ~ r1_orders_2(A_8,C_16,'#skF_3'(A_8,B_15,C_16))
      | r1_lattice3(A_8,B_15,C_16)
      | ~ m1_subset_1(C_16,u1_struct_0(A_8))
      | ~ l1_orders_2(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_159,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_7')
    | r1_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_24])).

tff(c_169,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_7')
    | r1_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_159])).

tff(c_170,plain,(
    ~ r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_169])).

tff(c_209,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_170])).

tff(c_210,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_7')
    | r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_212,plain,(
    ~ r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_210])).

tff(c_38,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_211,plain,(
    r1_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_84,plain,(
    ! [D_37,B_38] : r2_hidden(D_37,k2_tarski(D_37,B_38)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_87,plain,(
    ! [A_7] : r2_hidden(A_7,k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_84])).

tff(c_2652,plain,(
    ! [A_2570,C_2571,D_2572,B_2573] :
      ( r1_orders_2(A_2570,C_2571,D_2572)
      | ~ r2_hidden(D_2572,B_2573)
      | ~ m1_subset_1(D_2572,u1_struct_0(A_2570))
      | ~ r1_lattice3(A_2570,B_2573,C_2571)
      | ~ m1_subset_1(C_2571,u1_struct_0(A_2570))
      | ~ l1_orders_2(A_2570) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12144,plain,(
    ! [A_5176,C_5177,A_5178] :
      ( r1_orders_2(A_5176,C_5177,A_5178)
      | ~ m1_subset_1(A_5178,u1_struct_0(A_5176))
      | ~ r1_lattice3(A_5176,k1_tarski(A_5178),C_5177)
      | ~ m1_subset_1(C_5177,u1_struct_0(A_5176))
      | ~ l1_orders_2(A_5176) ) ),
    inference(resolution,[status(thm)],[c_87,c_2652])).

tff(c_12156,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_211,c_12144])).

tff(c_12160,plain,(
    r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_12156])).

tff(c_12162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_212,c_12160])).

tff(c_12163,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_210])).

tff(c_12170,plain,(
    ! [A_5236,A_5237,C_5238] :
      ( '#skF_4'(A_5236,k1_tarski(A_5237),C_5238) = A_5237
      | r2_lattice3(A_5236,k1_tarski(A_5237),C_5238)
      | ~ m1_subset_1(C_5238,u1_struct_0(A_5236))
      | ~ l1_orders_2(A_5236) ) ),
    inference(resolution,[status(thm)],[c_117,c_103])).

tff(c_12173,plain,
    ( '#skF_4'('#skF_5',k1_tarski('#skF_7'),'#skF_6') = '#skF_7'
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_12170,c_108])).

tff(c_12176,plain,(
    '#skF_4'('#skF_5',k1_tarski('#skF_7'),'#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_12173])).

tff(c_12183,plain,
    ( ~ r1_orders_2('#skF_5','#skF_7','#skF_6')
    | r2_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_12176,c_32])).

tff(c_12193,plain,(
    r2_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_12163,c_12183])).

tff(c_12195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_12193])).

tff(c_12196,plain,
    ( ~ r1_orders_2('#skF_5','#skF_7','#skF_6')
    | ~ r1_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6')
    | ~ r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_12204,plain,(
    ~ r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_12196])).

tff(c_12197,plain,(
    r2_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_50,plain,
    ( r1_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6')
    | r1_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ r1_orders_2('#skF_5','#skF_7','#skF_6')
    | ~ r2_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_12208,plain,
    ( r1_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6')
    | r1_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12197,c_50])).

tff(c_12209,plain,
    ( r1_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6')
    | ~ r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_12204,c_12208])).

tff(c_12210,plain,(
    ~ r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_12209])).

tff(c_13617,plain,(
    ! [A_7072,D_7073,C_7074,B_7075] :
      ( r1_orders_2(A_7072,D_7073,C_7074)
      | ~ r2_hidden(D_7073,B_7075)
      | ~ m1_subset_1(D_7073,u1_struct_0(A_7072))
      | ~ r2_lattice3(A_7072,B_7075,C_7074)
      | ~ m1_subset_1(C_7074,u1_struct_0(A_7072))
      | ~ l1_orders_2(A_7072) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_15928,plain,(
    ! [A_7827,A_7828,C_7829] :
      ( r1_orders_2(A_7827,A_7828,C_7829)
      | ~ m1_subset_1(A_7828,u1_struct_0(A_7827))
      | ~ r2_lattice3(A_7827,k1_tarski(A_7828),C_7829)
      | ~ m1_subset_1(C_7829,u1_struct_0(A_7827))
      | ~ l1_orders_2(A_7827) ) ),
    inference(resolution,[status(thm)],[c_87,c_13617])).

tff(c_15940,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_6')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_12197,c_15928])).

tff(c_15944,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_15940])).

tff(c_15946,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12210,c_15944])).

tff(c_15947,plain,(
    r1_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_12209])).

tff(c_17966,plain,(
    ! [A_10004,C_10005,D_10006,B_10007] :
      ( r1_orders_2(A_10004,C_10005,D_10006)
      | ~ r2_hidden(D_10006,B_10007)
      | ~ m1_subset_1(D_10006,u1_struct_0(A_10004))
      | ~ r1_lattice3(A_10004,B_10007,C_10005)
      | ~ m1_subset_1(C_10005,u1_struct_0(A_10004))
      | ~ l1_orders_2(A_10004) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_19694,plain,(
    ! [A_10506,C_10507,A_10508] :
      ( r1_orders_2(A_10506,C_10507,A_10508)
      | ~ m1_subset_1(A_10508,u1_struct_0(A_10506))
      | ~ r1_lattice3(A_10506,k1_tarski(A_10508),C_10507)
      | ~ m1_subset_1(C_10507,u1_struct_0(A_10506))
      | ~ l1_orders_2(A_10506) ) ),
    inference(resolution,[status(thm)],[c_87,c_17966])).

tff(c_19706,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_15947,c_19694])).

tff(c_19710,plain,(
    r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_19706])).

tff(c_19712,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12204,c_19710])).

tff(c_19713,plain,
    ( ~ r1_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6')
    | ~ r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_12196])).

tff(c_19715,plain,(
    ~ r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_19713])).

tff(c_21516,plain,(
    ! [A_12539,D_12540,C_12541,B_12542] :
      ( r1_orders_2(A_12539,D_12540,C_12541)
      | ~ r2_hidden(D_12540,B_12542)
      | ~ m1_subset_1(D_12540,u1_struct_0(A_12539))
      | ~ r2_lattice3(A_12539,B_12542,C_12541)
      | ~ m1_subset_1(C_12541,u1_struct_0(A_12539))
      | ~ l1_orders_2(A_12539) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_23628,plain,(
    ! [A_13344,A_13345,C_13346] :
      ( r1_orders_2(A_13344,A_13345,C_13346)
      | ~ m1_subset_1(A_13345,u1_struct_0(A_13344))
      | ~ r2_lattice3(A_13344,k1_tarski(A_13345),C_13346)
      | ~ m1_subset_1(C_13346,u1_struct_0(A_13344))
      | ~ l1_orders_2(A_13344) ) ),
    inference(resolution,[status(thm)],[c_87,c_21516])).

tff(c_23640,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_6')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_12197,c_23628])).

tff(c_23644,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_23640])).

tff(c_23646,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19715,c_23644])).

tff(c_23647,plain,(
    ~ r1_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_19713])).

tff(c_19714,plain,(
    r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_12196])).

tff(c_23666,plain,(
    ! [A_13407,B_13408,C_13409] :
      ( r2_hidden('#skF_3'(A_13407,B_13408,C_13409),B_13408)
      | r1_lattice3(A_13407,B_13408,C_13409)
      | ~ m1_subset_1(C_13409,u1_struct_0(A_13407))
      | ~ l1_orders_2(A_13407) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_23684,plain,(
    ! [A_13425,A_13426,C_13427] :
      ( '#skF_3'(A_13425,k1_tarski(A_13426),C_13427) = A_13426
      | r1_lattice3(A_13425,k1_tarski(A_13426),C_13427)
      | ~ m1_subset_1(C_13427,u1_struct_0(A_13425))
      | ~ l1_orders_2(A_13425) ) ),
    inference(resolution,[status(thm)],[c_23666,c_103])).

tff(c_23687,plain,
    ( '#skF_3'('#skF_5',k1_tarski('#skF_7'),'#skF_6') = '#skF_7'
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_23684,c_23647])).

tff(c_23690,plain,(
    '#skF_3'('#skF_5',k1_tarski('#skF_7'),'#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_23687])).

tff(c_23694,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_7')
    | r1_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_23690,c_24])).

tff(c_23704,plain,(
    r1_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_19714,c_23694])).

tff(c_23706,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_23647,c_23704])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:47:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.30/3.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.30/3.70  
% 10.30/3.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.30/3.70  %$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > m1_subset_1 > l1_orders_2 > k2_tarski > #nlpp > u1_struct_0 > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 10.30/3.70  
% 10.30/3.70  %Foreground sorts:
% 10.30/3.70  
% 10.30/3.70  
% 10.30/3.70  %Background operators:
% 10.30/3.70  
% 10.30/3.70  
% 10.30/3.70  %Foreground operators:
% 10.30/3.70  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 10.30/3.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.30/3.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.30/3.70  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.30/3.70  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 10.30/3.70  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 10.30/3.70  tff('#skF_7', type, '#skF_7': $i).
% 10.30/3.70  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 10.30/3.70  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.30/3.70  tff('#skF_5', type, '#skF_5': $i).
% 10.30/3.70  tff('#skF_6', type, '#skF_6': $i).
% 10.30/3.70  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.30/3.70  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 10.30/3.70  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 10.30/3.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.30/3.70  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 10.30/3.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.30/3.70  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.30/3.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.30/3.70  
% 10.49/3.72  tff(f_89, negated_conjecture, ~(![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((((r1_lattice3(A, k1_tarski(C), B) => r1_orders_2(A, B, C)) & (r1_orders_2(A, B, C) => r1_lattice3(A, k1_tarski(C), B))) & (r2_lattice3(A, k1_tarski(C), B) => r1_orders_2(A, C, B))) & (r1_orders_2(A, C, B) => r2_lattice3(A, k1_tarski(C), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_yellow_0)).
% 10.49/3.72  tff(f_64, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, D, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattice3)).
% 10.49/3.72  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 10.49/3.72  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 10.49/3.72  tff(f_50, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, C, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_lattice3)).
% 10.49/3.72  tff(c_44, plain, (~r1_orders_2('#skF_5', '#skF_6', '#skF_7') | ~r1_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6') | ~r1_orders_2('#skF_5', '#skF_7', '#skF_6') | ~r2_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.49/3.72  tff(c_108, plain, (~r2_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_44])).
% 10.49/3.72  tff(c_42, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.49/3.72  tff(c_40, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.49/3.72  tff(c_68, plain, (~r1_orders_2('#skF_5', '#skF_6', '#skF_7') | ~r1_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6') | r2_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6') | r1_orders_2('#skF_5', '#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.49/3.72  tff(c_142, plain, (~r1_orders_2('#skF_5', '#skF_6', '#skF_7') | ~r1_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6') | r1_orders_2('#skF_5', '#skF_7', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_108, c_68])).
% 10.49/3.72  tff(c_143, plain, (~r1_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_142])).
% 10.49/3.72  tff(c_74, plain, (r1_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6') | r1_orders_2('#skF_5', '#skF_6', '#skF_7') | r2_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6') | r1_orders_2('#skF_5', '#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.49/3.72  tff(c_175, plain, (r1_orders_2('#skF_5', '#skF_6', '#skF_7') | r1_orders_2('#skF_5', '#skF_7', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_108, c_143, c_74])).
% 10.49/3.72  tff(c_176, plain, (r1_orders_2('#skF_5', '#skF_7', '#skF_6')), inference(splitLeft, [status(thm)], [c_175])).
% 10.49/3.72  tff(c_117, plain, (![A_53, B_54, C_55]: (r2_hidden('#skF_4'(A_53, B_54, C_55), B_54) | r2_lattice3(A_53, B_54, C_55) | ~m1_subset_1(C_55, u1_struct_0(A_53)) | ~l1_orders_2(A_53))), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.49/3.72  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.49/3.72  tff(c_94, plain, (![D_42, B_43, A_44]: (D_42=B_43 | D_42=A_44 | ~r2_hidden(D_42, k2_tarski(A_44, B_43)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.49/3.72  tff(c_103, plain, (![D_42, A_7]: (D_42=A_7 | D_42=A_7 | ~r2_hidden(D_42, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_94])).
% 10.49/3.72  tff(c_177, plain, (![A_77, A_78, C_79]: ('#skF_4'(A_77, k1_tarski(A_78), C_79)=A_78 | r2_lattice3(A_77, k1_tarski(A_78), C_79) | ~m1_subset_1(C_79, u1_struct_0(A_77)) | ~l1_orders_2(A_77))), inference(resolution, [status(thm)], [c_117, c_103])).
% 10.49/3.72  tff(c_180, plain, ('#skF_4'('#skF_5', k1_tarski('#skF_7'), '#skF_6')='#skF_7' | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_177, c_108])).
% 10.49/3.72  tff(c_183, plain, ('#skF_4'('#skF_5', k1_tarski('#skF_7'), '#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_180])).
% 10.49/3.72  tff(c_32, plain, (![A_20, B_27, C_28]: (~r1_orders_2(A_20, '#skF_4'(A_20, B_27, C_28), C_28) | r2_lattice3(A_20, B_27, C_28) | ~m1_subset_1(C_28, u1_struct_0(A_20)) | ~l1_orders_2(A_20))), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.49/3.72  tff(c_193, plain, (~r1_orders_2('#skF_5', '#skF_7', '#skF_6') | r2_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_183, c_32])).
% 10.49/3.72  tff(c_203, plain, (r2_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_176, c_193])).
% 10.49/3.72  tff(c_205, plain, $false, inference(negUnitSimplification, [status(thm)], [c_108, c_203])).
% 10.49/3.72  tff(c_206, plain, (r1_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_175])).
% 10.49/3.72  tff(c_129, plain, (![A_59, B_60, C_61]: (r2_hidden('#skF_3'(A_59, B_60, C_61), B_60) | r1_lattice3(A_59, B_60, C_61) | ~m1_subset_1(C_61, u1_struct_0(A_59)) | ~l1_orders_2(A_59))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.49/3.72  tff(c_146, plain, (![A_74, A_75, C_76]: ('#skF_3'(A_74, k1_tarski(A_75), C_76)=A_75 | r1_lattice3(A_74, k1_tarski(A_75), C_76) | ~m1_subset_1(C_76, u1_struct_0(A_74)) | ~l1_orders_2(A_74))), inference(resolution, [status(thm)], [c_129, c_103])).
% 10.49/3.72  tff(c_149, plain, ('#skF_3'('#skF_5', k1_tarski('#skF_7'), '#skF_6')='#skF_7' | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_146, c_143])).
% 10.49/3.72  tff(c_152, plain, ('#skF_3'('#skF_5', k1_tarski('#skF_7'), '#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_149])).
% 10.49/3.72  tff(c_24, plain, (![A_8, C_16, B_15]: (~r1_orders_2(A_8, C_16, '#skF_3'(A_8, B_15, C_16)) | r1_lattice3(A_8, B_15, C_16) | ~m1_subset_1(C_16, u1_struct_0(A_8)) | ~l1_orders_2(A_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.49/3.72  tff(c_159, plain, (~r1_orders_2('#skF_5', '#skF_6', '#skF_7') | r1_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_152, c_24])).
% 10.49/3.72  tff(c_169, plain, (~r1_orders_2('#skF_5', '#skF_6', '#skF_7') | r1_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_159])).
% 10.49/3.72  tff(c_170, plain, (~r1_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_143, c_169])).
% 10.49/3.72  tff(c_209, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_206, c_170])).
% 10.49/3.72  tff(c_210, plain, (~r1_orders_2('#skF_5', '#skF_6', '#skF_7') | r1_orders_2('#skF_5', '#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_142])).
% 10.49/3.72  tff(c_212, plain, (~r1_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_210])).
% 10.49/3.72  tff(c_38, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.49/3.72  tff(c_211, plain, (r1_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_142])).
% 10.49/3.72  tff(c_84, plain, (![D_37, B_38]: (r2_hidden(D_37, k2_tarski(D_37, B_38)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.49/3.72  tff(c_87, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_84])).
% 10.49/3.72  tff(c_2652, plain, (![A_2570, C_2571, D_2572, B_2573]: (r1_orders_2(A_2570, C_2571, D_2572) | ~r2_hidden(D_2572, B_2573) | ~m1_subset_1(D_2572, u1_struct_0(A_2570)) | ~r1_lattice3(A_2570, B_2573, C_2571) | ~m1_subset_1(C_2571, u1_struct_0(A_2570)) | ~l1_orders_2(A_2570))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.49/3.72  tff(c_12144, plain, (![A_5176, C_5177, A_5178]: (r1_orders_2(A_5176, C_5177, A_5178) | ~m1_subset_1(A_5178, u1_struct_0(A_5176)) | ~r1_lattice3(A_5176, k1_tarski(A_5178), C_5177) | ~m1_subset_1(C_5177, u1_struct_0(A_5176)) | ~l1_orders_2(A_5176))), inference(resolution, [status(thm)], [c_87, c_2652])).
% 10.49/3.72  tff(c_12156, plain, (r1_orders_2('#skF_5', '#skF_6', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_211, c_12144])).
% 10.49/3.72  tff(c_12160, plain, (r1_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_12156])).
% 10.49/3.72  tff(c_12162, plain, $false, inference(negUnitSimplification, [status(thm)], [c_212, c_12160])).
% 10.49/3.72  tff(c_12163, plain, (r1_orders_2('#skF_5', '#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_210])).
% 10.49/3.72  tff(c_12170, plain, (![A_5236, A_5237, C_5238]: ('#skF_4'(A_5236, k1_tarski(A_5237), C_5238)=A_5237 | r2_lattice3(A_5236, k1_tarski(A_5237), C_5238) | ~m1_subset_1(C_5238, u1_struct_0(A_5236)) | ~l1_orders_2(A_5236))), inference(resolution, [status(thm)], [c_117, c_103])).
% 10.49/3.72  tff(c_12173, plain, ('#skF_4'('#skF_5', k1_tarski('#skF_7'), '#skF_6')='#skF_7' | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_12170, c_108])).
% 10.49/3.72  tff(c_12176, plain, ('#skF_4'('#skF_5', k1_tarski('#skF_7'), '#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_12173])).
% 10.49/3.72  tff(c_12183, plain, (~r1_orders_2('#skF_5', '#skF_7', '#skF_6') | r2_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_12176, c_32])).
% 10.49/3.72  tff(c_12193, plain, (r2_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_12163, c_12183])).
% 10.49/3.72  tff(c_12195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_108, c_12193])).
% 10.49/3.72  tff(c_12196, plain, (~r1_orders_2('#skF_5', '#skF_7', '#skF_6') | ~r1_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6') | ~r1_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_44])).
% 10.49/3.72  tff(c_12204, plain, (~r1_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_12196])).
% 10.49/3.72  tff(c_12197, plain, (r2_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_44])).
% 10.49/3.72  tff(c_50, plain, (r1_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6') | r1_orders_2('#skF_5', '#skF_6', '#skF_7') | ~r1_orders_2('#skF_5', '#skF_7', '#skF_6') | ~r2_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.49/3.72  tff(c_12208, plain, (r1_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6') | r1_orders_2('#skF_5', '#skF_6', '#skF_7') | ~r1_orders_2('#skF_5', '#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_12197, c_50])).
% 10.49/3.72  tff(c_12209, plain, (r1_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6') | ~r1_orders_2('#skF_5', '#skF_7', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_12204, c_12208])).
% 10.49/3.72  tff(c_12210, plain, (~r1_orders_2('#skF_5', '#skF_7', '#skF_6')), inference(splitLeft, [status(thm)], [c_12209])).
% 10.49/3.72  tff(c_13617, plain, (![A_7072, D_7073, C_7074, B_7075]: (r1_orders_2(A_7072, D_7073, C_7074) | ~r2_hidden(D_7073, B_7075) | ~m1_subset_1(D_7073, u1_struct_0(A_7072)) | ~r2_lattice3(A_7072, B_7075, C_7074) | ~m1_subset_1(C_7074, u1_struct_0(A_7072)) | ~l1_orders_2(A_7072))), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.49/3.72  tff(c_15928, plain, (![A_7827, A_7828, C_7829]: (r1_orders_2(A_7827, A_7828, C_7829) | ~m1_subset_1(A_7828, u1_struct_0(A_7827)) | ~r2_lattice3(A_7827, k1_tarski(A_7828), C_7829) | ~m1_subset_1(C_7829, u1_struct_0(A_7827)) | ~l1_orders_2(A_7827))), inference(resolution, [status(thm)], [c_87, c_13617])).
% 10.49/3.72  tff(c_15940, plain, (r1_orders_2('#skF_5', '#skF_7', '#skF_6') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_12197, c_15928])).
% 10.49/3.72  tff(c_15944, plain, (r1_orders_2('#skF_5', '#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_15940])).
% 10.49/3.72  tff(c_15946, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12210, c_15944])).
% 10.49/3.72  tff(c_15947, plain, (r1_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_12209])).
% 10.49/3.72  tff(c_17966, plain, (![A_10004, C_10005, D_10006, B_10007]: (r1_orders_2(A_10004, C_10005, D_10006) | ~r2_hidden(D_10006, B_10007) | ~m1_subset_1(D_10006, u1_struct_0(A_10004)) | ~r1_lattice3(A_10004, B_10007, C_10005) | ~m1_subset_1(C_10005, u1_struct_0(A_10004)) | ~l1_orders_2(A_10004))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.49/3.72  tff(c_19694, plain, (![A_10506, C_10507, A_10508]: (r1_orders_2(A_10506, C_10507, A_10508) | ~m1_subset_1(A_10508, u1_struct_0(A_10506)) | ~r1_lattice3(A_10506, k1_tarski(A_10508), C_10507) | ~m1_subset_1(C_10507, u1_struct_0(A_10506)) | ~l1_orders_2(A_10506))), inference(resolution, [status(thm)], [c_87, c_17966])).
% 10.49/3.72  tff(c_19706, plain, (r1_orders_2('#skF_5', '#skF_6', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_15947, c_19694])).
% 10.49/3.72  tff(c_19710, plain, (r1_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_19706])).
% 10.49/3.72  tff(c_19712, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12204, c_19710])).
% 10.49/3.72  tff(c_19713, plain, (~r1_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6') | ~r1_orders_2('#skF_5', '#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_12196])).
% 10.49/3.72  tff(c_19715, plain, (~r1_orders_2('#skF_5', '#skF_7', '#skF_6')), inference(splitLeft, [status(thm)], [c_19713])).
% 10.49/3.72  tff(c_21516, plain, (![A_12539, D_12540, C_12541, B_12542]: (r1_orders_2(A_12539, D_12540, C_12541) | ~r2_hidden(D_12540, B_12542) | ~m1_subset_1(D_12540, u1_struct_0(A_12539)) | ~r2_lattice3(A_12539, B_12542, C_12541) | ~m1_subset_1(C_12541, u1_struct_0(A_12539)) | ~l1_orders_2(A_12539))), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.49/3.72  tff(c_23628, plain, (![A_13344, A_13345, C_13346]: (r1_orders_2(A_13344, A_13345, C_13346) | ~m1_subset_1(A_13345, u1_struct_0(A_13344)) | ~r2_lattice3(A_13344, k1_tarski(A_13345), C_13346) | ~m1_subset_1(C_13346, u1_struct_0(A_13344)) | ~l1_orders_2(A_13344))), inference(resolution, [status(thm)], [c_87, c_21516])).
% 10.49/3.72  tff(c_23640, plain, (r1_orders_2('#skF_5', '#skF_7', '#skF_6') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_12197, c_23628])).
% 10.49/3.72  tff(c_23644, plain, (r1_orders_2('#skF_5', '#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_23640])).
% 10.49/3.72  tff(c_23646, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19715, c_23644])).
% 10.49/3.72  tff(c_23647, plain, (~r1_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_19713])).
% 10.49/3.72  tff(c_19714, plain, (r1_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_12196])).
% 10.49/3.72  tff(c_23666, plain, (![A_13407, B_13408, C_13409]: (r2_hidden('#skF_3'(A_13407, B_13408, C_13409), B_13408) | r1_lattice3(A_13407, B_13408, C_13409) | ~m1_subset_1(C_13409, u1_struct_0(A_13407)) | ~l1_orders_2(A_13407))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.49/3.72  tff(c_23684, plain, (![A_13425, A_13426, C_13427]: ('#skF_3'(A_13425, k1_tarski(A_13426), C_13427)=A_13426 | r1_lattice3(A_13425, k1_tarski(A_13426), C_13427) | ~m1_subset_1(C_13427, u1_struct_0(A_13425)) | ~l1_orders_2(A_13425))), inference(resolution, [status(thm)], [c_23666, c_103])).
% 10.49/3.72  tff(c_23687, plain, ('#skF_3'('#skF_5', k1_tarski('#skF_7'), '#skF_6')='#skF_7' | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_23684, c_23647])).
% 10.49/3.72  tff(c_23690, plain, ('#skF_3'('#skF_5', k1_tarski('#skF_7'), '#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_23687])).
% 10.49/3.72  tff(c_23694, plain, (~r1_orders_2('#skF_5', '#skF_6', '#skF_7') | r1_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_23690, c_24])).
% 10.49/3.72  tff(c_23704, plain, (r1_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_19714, c_23694])).
% 10.49/3.72  tff(c_23706, plain, $false, inference(negUnitSimplification, [status(thm)], [c_23647, c_23704])).
% 10.49/3.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.49/3.72  
% 10.49/3.72  Inference rules
% 10.49/3.72  ----------------------
% 10.49/3.72  #Ref     : 0
% 10.49/3.72  #Sup     : 4009
% 10.49/3.72  #Fact    : 136
% 10.49/3.72  #Define  : 0
% 10.49/3.72  #Split   : 25
% 10.49/3.72  #Chain   : 0
% 10.49/3.72  #Close   : 0
% 10.49/3.72  
% 10.49/3.72  Ordering : KBO
% 10.49/3.72  
% 10.49/3.72  Simplification rules
% 10.49/3.72  ----------------------
% 10.49/3.72  #Subsume      : 1825
% 10.49/3.72  #Demod        : 405
% 10.49/3.72  #Tautology    : 1216
% 10.49/3.72  #SimpNegUnit  : 412
% 10.49/3.72  #BackRed      : 0
% 10.49/3.72  
% 10.49/3.72  #Partial instantiations: 8040
% 10.49/3.72  #Strategies tried      : 1
% 10.49/3.72  
% 10.49/3.72  Timing (in seconds)
% 10.49/3.72  ----------------------
% 10.49/3.72  Preprocessing        : 0.31
% 10.49/3.72  Parsing              : 0.15
% 10.49/3.72  CNF conversion       : 0.03
% 10.49/3.72  Main loop            : 2.58
% 10.49/3.72  Inferencing          : 1.17
% 10.49/3.72  Reduction            : 0.55
% 10.49/3.72  Demodulation         : 0.36
% 10.49/3.72  BG Simplification    : 0.11
% 10.49/3.72  Subsumption          : 0.61
% 10.49/3.72  Abstraction          : 0.16
% 10.49/3.72  MUC search           : 0.00
% 10.49/3.72  Cooper               : 0.00
% 10.49/3.72  Total                : 2.93
% 10.49/3.72  Index Insertion      : 0.00
% 10.49/3.72  Index Deletion       : 0.00
% 10.49/3.72  Index Matching       : 0.00
% 10.49/3.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
