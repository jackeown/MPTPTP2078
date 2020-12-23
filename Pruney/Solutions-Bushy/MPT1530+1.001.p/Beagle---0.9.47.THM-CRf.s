%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1530+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:00 EST 2020

% Result     : Theorem 36.40s
% Output     : CNFRefutation 36.64s
% Verified   : 
% Statistics : Number of formulae       :  191 ( 756 expanded)
%              Number of leaves         :   23 ( 239 expanded)
%              Depth                    :   11
%              Number of atoms          :  451 (4358 expanded)
%              Number of equality atoms :   37 ( 126 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > m1_subset_1 > l1_orders_2 > k2_tarski > #nlpp > u1_struct_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_3

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

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( ( r1_lattice3(A,k2_tarski(C,D),B)
                       => ( r1_orders_2(A,B,C)
                          & r1_orders_2(A,B,D) ) )
                      & ( ( r1_orders_2(A,B,C)
                          & r1_orders_2(A,B,D) )
                       => r1_lattice3(A,k2_tarski(C,D),B) )
                      & ( r2_lattice3(A,k2_tarski(C,D),B)
                       => ( r1_orders_2(A,C,B)
                          & r1_orders_2(A,D,B) ) )
                      & ( ( r1_orders_2(A,C,B)
                          & r1_orders_2(A,D,B) )
                       => r2_lattice3(A,k2_tarski(C,D),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_yellow_0)).

tff(f_61,axiom,(
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

tff(f_33,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

tff(c_110,plain,
    ( r1_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6')
    | r1_orders_2('#skF_5','#skF_6','#skF_8')
    | r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6')
    | r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1280,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_86,plain,
    ( r1_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6')
    | r1_orders_2('#skF_5','#skF_6','#skF_8')
    | r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6')
    | r1_orders_2('#skF_5','#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_130,plain,(
    r1_orders_2('#skF_5','#skF_8','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_50,plain,
    ( r1_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6')
    | r1_orders_2('#skF_5','#skF_6','#skF_8')
    | ~ r1_orders_2('#skF_5','#skF_8','#skF_6')
    | ~ r1_orders_2('#skF_5','#skF_7','#skF_6')
    | ~ r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1616,plain,
    ( r1_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6')
    | r1_orders_2('#skF_5','#skF_6','#skF_8')
    | ~ r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1280,c_130,c_50])).

tff(c_1617,plain,(
    ~ r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1616])).

tff(c_42,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_131,plain,(
    ! [A_55,B_56,C_57] :
      ( r2_hidden('#skF_4'(A_55,B_56,C_57),B_56)
      | r2_lattice3(A_55,B_56,C_57)
      | ~ m1_subset_1(C_57,u1_struct_0(A_55))
      | ~ l1_orders_2(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    ! [D_6,B_2,A_1] :
      ( D_6 = B_2
      | D_6 = A_1
      | ~ r2_hidden(D_6,k2_tarski(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_35718,plain,(
    ! [A_10094,A_10095,B_10096,C_10097] :
      ( '#skF_4'(A_10094,k2_tarski(A_10095,B_10096),C_10097) = B_10096
      | '#skF_4'(A_10094,k2_tarski(A_10095,B_10096),C_10097) = A_10095
      | r2_lattice3(A_10094,k2_tarski(A_10095,B_10096),C_10097)
      | ~ m1_subset_1(C_10097,u1_struct_0(A_10094))
      | ~ l1_orders_2(A_10094) ) ),
    inference(resolution,[status(thm)],[c_131,c_2])).

tff(c_35735,plain,
    ( '#skF_4'('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') = '#skF_8'
    | '#skF_4'('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') = '#skF_7'
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_35718,c_1617])).

tff(c_36373,plain,
    ( '#skF_4'('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') = '#skF_8'
    | '#skF_4'('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_35735])).

tff(c_36374,plain,(
    '#skF_4'('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_36373])).

tff(c_30,plain,(
    ! [A_19,B_26,C_27] :
      ( ~ r1_orders_2(A_19,'#skF_4'(A_19,B_26,C_27),C_27)
      | r2_lattice3(A_19,B_26,C_27)
      | ~ m1_subset_1(C_27,u1_struct_0(A_19))
      | ~ l1_orders_2(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_36378,plain,
    ( ~ r1_orders_2('#skF_5','#skF_7','#skF_6')
    | r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_36374,c_30])).

tff(c_37044,plain,(
    r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1280,c_36378])).

tff(c_37046,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1617,c_37044])).

tff(c_37047,plain,(
    '#skF_4'('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_36373])).

tff(c_37052,plain,
    ( ~ r1_orders_2('#skF_5','#skF_8','#skF_6')
    | r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_37047,c_30])).

tff(c_37718,plain,(
    r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_130,c_37052])).

tff(c_37720,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1617,c_37718])).

tff(c_37722,plain,(
    r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_1616])).

tff(c_37721,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_8')
    | r1_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_1616])).

tff(c_37801,plain,(
    r1_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_37721])).

tff(c_44,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_8')
    | ~ r1_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ r1_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6')
    | ~ r1_orders_2('#skF_5','#skF_8','#skF_6')
    | ~ r1_orders_2('#skF_5','#skF_7','#skF_6')
    | ~ r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_38997,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_8')
    | ~ r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37722,c_1280,c_130,c_37801,c_44])).

tff(c_38998,plain,(
    ~ r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_38997])).

tff(c_38,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_6,plain,(
    ! [D_6,B_2] : r2_hidden(D_6,k2_tarski(D_6,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_38443,plain,(
    ! [A_10829,C_10830,D_10831,B_10832] :
      ( r1_orders_2(A_10829,C_10830,D_10831)
      | ~ r2_hidden(D_10831,B_10832)
      | ~ m1_subset_1(D_10831,u1_struct_0(A_10829))
      | ~ r1_lattice3(A_10829,B_10832,C_10830)
      | ~ m1_subset_1(C_10830,u1_struct_0(A_10829))
      | ~ l1_orders_2(A_10829) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_40785,plain,(
    ! [A_12088,C_12089,D_12090,B_12091] :
      ( r1_orders_2(A_12088,C_12089,D_12090)
      | ~ m1_subset_1(D_12090,u1_struct_0(A_12088))
      | ~ r1_lattice3(A_12088,k2_tarski(D_12090,B_12091),C_12089)
      | ~ m1_subset_1(C_12089,u1_struct_0(A_12088))
      | ~ l1_orders_2(A_12088) ) ),
    inference(resolution,[status(thm)],[c_6,c_38443])).

tff(c_40788,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_37801,c_40785])).

tff(c_40803,plain,(
    r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_40788])).

tff(c_40805,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38998,c_40803])).

tff(c_40806,plain,(
    ~ r1_orders_2('#skF_5','#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_38997])).

tff(c_36,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_4,plain,(
    ! [D_6,A_1] : r2_hidden(D_6,k2_tarski(A_1,D_6)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_42594,plain,(
    ! [A_13157,C_13158,D_13159,A_13160] :
      ( r1_orders_2(A_13157,C_13158,D_13159)
      | ~ m1_subset_1(D_13159,u1_struct_0(A_13157))
      | ~ r1_lattice3(A_13157,k2_tarski(A_13160,D_13159),C_13158)
      | ~ m1_subset_1(C_13158,u1_struct_0(A_13157))
      | ~ l1_orders_2(A_13157) ) ),
    inference(resolution,[status(thm)],[c_4,c_38443])).

tff(c_42597,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_37801,c_42594])).

tff(c_42612,plain,(
    r1_orders_2('#skF_5','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_42597])).

tff(c_42614,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40806,c_42612])).

tff(c_42616,plain,(
    ~ r1_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_37721])).

tff(c_42615,plain,(
    r1_orders_2('#skF_5','#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_37721])).

tff(c_54,plain,
    ( r1_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6')
    | r1_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ r1_orders_2('#skF_5','#skF_8','#skF_6')
    | ~ r1_orders_2('#skF_5','#skF_7','#skF_6')
    | ~ r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_43191,plain,
    ( r1_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6')
    | r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37722,c_1280,c_130,c_54])).

tff(c_43192,plain,(
    r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_42616,c_43191])).

tff(c_137,plain,(
    ! [A_58,B_59,C_60] :
      ( r2_hidden('#skF_3'(A_58,B_59,C_60),B_59)
      | r1_lattice3(A_58,B_59,C_60)
      | ~ m1_subset_1(C_60,u1_struct_0(A_58))
      | ~ l1_orders_2(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_101279,plain,(
    ! [A_27992,A_27993,B_27994,C_27995] :
      ( '#skF_3'(A_27992,k2_tarski(A_27993,B_27994),C_27995) = B_27994
      | '#skF_3'(A_27992,k2_tarski(A_27993,B_27994),C_27995) = A_27993
      | r1_lattice3(A_27992,k2_tarski(A_27993,B_27994),C_27995)
      | ~ m1_subset_1(C_27995,u1_struct_0(A_27992))
      | ~ l1_orders_2(A_27992) ) ),
    inference(resolution,[status(thm)],[c_137,c_2])).

tff(c_101296,plain,
    ( '#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') = '#skF_8'
    | '#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') = '#skF_7'
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_101279,c_42616])).

tff(c_102105,plain,
    ( '#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') = '#skF_8'
    | '#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_101296])).

tff(c_102106,plain,(
    '#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_102105])).

tff(c_22,plain,(
    ! [A_7,C_15,B_14] :
      ( ~ r1_orders_2(A_7,C_15,'#skF_3'(A_7,B_14,C_15))
      | r1_lattice3(A_7,B_14,C_15)
      | ~ m1_subset_1(C_15,u1_struct_0(A_7))
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_102113,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_7')
    | r1_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_102106,c_22])).

tff(c_102977,plain,(
    r1_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_43192,c_102113])).

tff(c_102979,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42616,c_102977])).

tff(c_102980,plain,(
    '#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_102105])).

tff(c_102988,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_8')
    | r1_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_102980,c_22])).

tff(c_103852,plain,(
    r1_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_42615,c_102988])).

tff(c_103854,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42616,c_103852])).

tff(c_103856,plain,(
    ~ r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_103855,plain,
    ( r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6')
    | r1_orders_2('#skF_5','#skF_6','#skF_8')
    | r1_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_103861,plain,(
    r1_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_103855])).

tff(c_104,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_8')
    | ~ r1_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ r1_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6')
    | r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6')
    | r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_104441,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_8')
    | ~ r1_orders_2('#skF_5','#skF_6','#skF_7')
    | r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6')
    | r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103861,c_104])).

tff(c_104442,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_8')
    | ~ r1_orders_2('#skF_5','#skF_6','#skF_7')
    | r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_103856,c_104441])).

tff(c_104443,plain,(
    ~ r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_104442])).

tff(c_104718,plain,(
    ! [A_29004,C_29005,D_29006,B_29007] :
      ( r1_orders_2(A_29004,C_29005,D_29006)
      | ~ r2_hidden(D_29006,B_29007)
      | ~ m1_subset_1(D_29006,u1_struct_0(A_29004))
      | ~ r1_lattice3(A_29004,B_29007,C_29005)
      | ~ m1_subset_1(C_29005,u1_struct_0(A_29004))
      | ~ l1_orders_2(A_29004) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_107173,plain,(
    ! [A_30265,C_30266,D_30267,B_30268] :
      ( r1_orders_2(A_30265,C_30266,D_30267)
      | ~ m1_subset_1(D_30267,u1_struct_0(A_30265))
      | ~ r1_lattice3(A_30265,k2_tarski(D_30267,B_30268),C_30266)
      | ~ m1_subset_1(C_30266,u1_struct_0(A_30265))
      | ~ l1_orders_2(A_30265) ) ),
    inference(resolution,[status(thm)],[c_6,c_104718])).

tff(c_107176,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_103861,c_107173])).

tff(c_107191,plain,(
    r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_107176])).

tff(c_107193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104443,c_107191])).

tff(c_107194,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_8')
    | r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_104442])).

tff(c_107196,plain,(
    ~ r1_orders_2('#skF_5','#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_107194])).

tff(c_107197,plain,(
    ! [A_30404,C_30405,D_30406,B_30407] :
      ( r1_orders_2(A_30404,C_30405,D_30406)
      | ~ r2_hidden(D_30406,B_30407)
      | ~ m1_subset_1(D_30406,u1_struct_0(A_30404))
      | ~ r1_lattice3(A_30404,B_30407,C_30405)
      | ~ m1_subset_1(C_30405,u1_struct_0(A_30404))
      | ~ l1_orders_2(A_30404) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_109912,plain,(
    ! [A_31665,C_31666,D_31667,A_31668] :
      ( r1_orders_2(A_31665,C_31666,D_31667)
      | ~ m1_subset_1(D_31667,u1_struct_0(A_31665))
      | ~ r1_lattice3(A_31665,k2_tarski(A_31668,D_31667),C_31666)
      | ~ m1_subset_1(C_31666,u1_struct_0(A_31665))
      | ~ l1_orders_2(A_31665) ) ),
    inference(resolution,[status(thm)],[c_4,c_107197])).

tff(c_109915,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_103861,c_109912])).

tff(c_109930,plain,(
    r1_orders_2('#skF_5','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_109915])).

tff(c_109932,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107196,c_109930])).

tff(c_109933,plain,(
    r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_107194])).

tff(c_110439,plain,(
    ! [A_31945,D_31946,C_31947,B_31948] :
      ( r1_orders_2(A_31945,D_31946,C_31947)
      | ~ r2_hidden(D_31946,B_31948)
      | ~ m1_subset_1(D_31946,u1_struct_0(A_31945))
      | ~ r2_lattice3(A_31945,B_31948,C_31947)
      | ~ m1_subset_1(C_31947,u1_struct_0(A_31945))
      | ~ l1_orders_2(A_31945) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_112695,plain,(
    ! [A_32967,D_32968,C_32969,B_32970] :
      ( r1_orders_2(A_32967,D_32968,C_32969)
      | ~ m1_subset_1(D_32968,u1_struct_0(A_32967))
      | ~ r2_lattice3(A_32967,k2_tarski(D_32968,B_32970),C_32969)
      | ~ m1_subset_1(C_32969,u1_struct_0(A_32967))
      | ~ l1_orders_2(A_32967) ) ),
    inference(resolution,[status(thm)],[c_6,c_110439])).

tff(c_112698,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_6')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_109933,c_112695])).

tff(c_112713,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_112698])).

tff(c_112715,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103856,c_112713])).

tff(c_112717,plain,(
    ~ r1_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_103855])).

tff(c_112716,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_8')
    | r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_103855])).

tff(c_112727,plain,(
    r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_112716])).

tff(c_113706,plain,(
    ! [A_33486,D_33487,C_33488,B_33489] :
      ( r1_orders_2(A_33486,D_33487,C_33488)
      | ~ r2_hidden(D_33487,B_33489)
      | ~ m1_subset_1(D_33487,u1_struct_0(A_33486))
      | ~ r2_lattice3(A_33486,B_33489,C_33488)
      | ~ m1_subset_1(C_33488,u1_struct_0(A_33486))
      | ~ l1_orders_2(A_33486) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_116008,plain,(
    ! [A_34649,D_34650,C_34651,B_34652] :
      ( r1_orders_2(A_34649,D_34650,C_34651)
      | ~ m1_subset_1(D_34650,u1_struct_0(A_34649))
      | ~ r2_lattice3(A_34649,k2_tarski(D_34650,B_34652),C_34651)
      | ~ m1_subset_1(C_34651,u1_struct_0(A_34649))
      | ~ l1_orders_2(A_34649) ) ),
    inference(resolution,[status(thm)],[c_6,c_113706])).

tff(c_116011,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_6')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_112727,c_116008])).

tff(c_116026,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_116011])).

tff(c_116028,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103856,c_116026])).

tff(c_116029,plain,(
    r1_orders_2('#skF_5','#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_112716])).

tff(c_116030,plain,(
    ~ r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_112716])).

tff(c_114,plain,
    ( r1_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6')
    | r1_orders_2('#skF_5','#skF_6','#skF_7')
    | r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6')
    | r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_103857,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_103858,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103856,c_103857])).

tff(c_103859,plain,
    ( r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6')
    | r1_orders_2('#skF_5','#skF_6','#skF_7')
    | r1_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_116043,plain,(
    r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_112717,c_116030,c_103859])).

tff(c_193507,plain,(
    ! [A_53460,A_53461,B_53462,C_53463] :
      ( '#skF_3'(A_53460,k2_tarski(A_53461,B_53462),C_53463) = B_53462
      | '#skF_3'(A_53460,k2_tarski(A_53461,B_53462),C_53463) = A_53461
      | r1_lattice3(A_53460,k2_tarski(A_53461,B_53462),C_53463)
      | ~ m1_subset_1(C_53463,u1_struct_0(A_53460))
      | ~ l1_orders_2(A_53460) ) ),
    inference(resolution,[status(thm)],[c_137,c_2])).

tff(c_193524,plain,
    ( '#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') = '#skF_8'
    | '#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') = '#skF_7'
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_193507,c_112717])).

tff(c_194351,plain,
    ( '#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') = '#skF_8'
    | '#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_193524])).

tff(c_194352,plain,(
    '#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_194351])).

tff(c_194359,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_7')
    | r1_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_194352,c_22])).

tff(c_195232,plain,(
    r1_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_116043,c_194359])).

tff(c_195234,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112717,c_195232])).

tff(c_195235,plain,(
    '#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_194351])).

tff(c_195243,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_8')
    | r1_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_195235,c_22])).

tff(c_196116,plain,(
    r1_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_116029,c_195243])).

tff(c_196118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112717,c_196116])).

tff(c_196120,plain,(
    ~ r1_orders_2('#skF_5','#skF_8','#skF_6') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_90,plain,
    ( r1_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6')
    | r1_orders_2('#skF_5','#skF_6','#skF_7')
    | r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6')
    | r1_orders_2('#skF_5','#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_196121,plain,(
    r1_orders_2('#skF_5','#skF_8','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_196122,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_196120,c_196121])).

tff(c_196123,plain,
    ( r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6')
    | r1_orders_2('#skF_5','#skF_6','#skF_7')
    | r1_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_196125,plain,(
    r1_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_196123])).

tff(c_198292,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_8')
    | ~ r1_orders_2('#skF_5','#skF_6','#skF_7')
    | r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6')
    | r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_196125,c_104])).

tff(c_198293,plain,(
    ~ r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_198292])).

tff(c_198630,plain,(
    ! [A_55730,C_55731,D_55732,B_55733] :
      ( r1_orders_2(A_55730,C_55731,D_55732)
      | ~ r2_hidden(D_55732,B_55733)
      | ~ m1_subset_1(D_55732,u1_struct_0(A_55730))
      | ~ r1_lattice3(A_55730,B_55733,C_55731)
      | ~ m1_subset_1(C_55731,u1_struct_0(A_55730))
      | ~ l1_orders_2(A_55730) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_200558,plain,(
    ! [A_56703,C_56704,D_56705,B_56706] :
      ( r1_orders_2(A_56703,C_56704,D_56705)
      | ~ m1_subset_1(D_56705,u1_struct_0(A_56703))
      | ~ r1_lattice3(A_56703,k2_tarski(D_56705,B_56706),C_56704)
      | ~ m1_subset_1(C_56704,u1_struct_0(A_56703))
      | ~ l1_orders_2(A_56703) ) ),
    inference(resolution,[status(thm)],[c_6,c_198630])).

tff(c_200573,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_196125,c_200558])).

tff(c_200576,plain,(
    r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_200573])).

tff(c_200578,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_198293,c_200576])).

tff(c_200580,plain,(
    r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_198292])).

tff(c_80,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_8')
    | ~ r1_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ r1_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6')
    | r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6')
    | r1_orders_2('#skF_5','#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_200582,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_8')
    | ~ r1_orders_2('#skF_5','#skF_6','#skF_7')
    | r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6')
    | r1_orders_2('#skF_5','#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_196125,c_80])).

tff(c_200583,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_8')
    | ~ r1_orders_2('#skF_5','#skF_6','#skF_7')
    | r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_196120,c_200582])).

tff(c_200584,plain,(
    ~ r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_200583])).

tff(c_200586,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_200580,c_200584])).

tff(c_200587,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_8')
    | r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_200583])).

tff(c_200590,plain,(
    ~ r1_orders_2('#skF_5','#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_200587])).

tff(c_201027,plain,(
    ! [A_57028,C_57029,D_57030,B_57031] :
      ( r1_orders_2(A_57028,C_57029,D_57030)
      | ~ r2_hidden(D_57030,B_57031)
      | ~ m1_subset_1(D_57030,u1_struct_0(A_57028))
      | ~ r1_lattice3(A_57028,B_57031,C_57029)
      | ~ m1_subset_1(C_57029,u1_struct_0(A_57028))
      | ~ l1_orders_2(A_57028) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_202846,plain,(
    ! [A_57909,C_57910,D_57911,A_57912] :
      ( r1_orders_2(A_57909,C_57910,D_57911)
      | ~ m1_subset_1(D_57911,u1_struct_0(A_57909))
      | ~ r1_lattice3(A_57909,k2_tarski(A_57912,D_57911),C_57910)
      | ~ m1_subset_1(C_57910,u1_struct_0(A_57909))
      | ~ l1_orders_2(A_57909) ) ),
    inference(resolution,[status(thm)],[c_4,c_201027])).

tff(c_202861,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_196125,c_202846])).

tff(c_202864,plain,(
    r1_orders_2('#skF_5','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_202861])).

tff(c_202866,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_200590,c_202864])).

tff(c_202867,plain,(
    r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_200587])).

tff(c_198100,plain,(
    ! [A_55495,D_55496,C_55497,B_55498] :
      ( r1_orders_2(A_55495,D_55496,C_55497)
      | ~ r2_hidden(D_55496,B_55498)
      | ~ m1_subset_1(D_55496,u1_struct_0(A_55495))
      | ~ r2_lattice3(A_55495,B_55498,C_55497)
      | ~ m1_subset_1(C_55497,u1_struct_0(A_55495))
      | ~ l1_orders_2(A_55495) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_205228,plain,(
    ! [A_59119,D_59120,C_59121,A_59122] :
      ( r1_orders_2(A_59119,D_59120,C_59121)
      | ~ m1_subset_1(D_59120,u1_struct_0(A_59119))
      | ~ r2_lattice3(A_59119,k2_tarski(A_59122,D_59120),C_59121)
      | ~ m1_subset_1(C_59121,u1_struct_0(A_59119))
      | ~ l1_orders_2(A_59119) ) ),
    inference(resolution,[status(thm)],[c_4,c_198100])).

tff(c_205231,plain,
    ( r1_orders_2('#skF_5','#skF_8','#skF_6')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_202867,c_205228])).

tff(c_205246,plain,(
    r1_orders_2('#skF_5','#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_205231])).

tff(c_205248,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_196120,c_205246])).

tff(c_205250,plain,(
    ~ r1_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_196123])).

tff(c_205249,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_7')
    | r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_196123])).

tff(c_205251,plain,(
    r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_205249])).

tff(c_206993,plain,(
    ! [A_60655,D_60656,C_60657,B_60658] :
      ( r1_orders_2(A_60655,D_60656,C_60657)
      | ~ r2_hidden(D_60656,B_60658)
      | ~ m1_subset_1(D_60656,u1_struct_0(A_60655))
      | ~ r2_lattice3(A_60655,B_60658,C_60657)
      | ~ m1_subset_1(C_60657,u1_struct_0(A_60655))
      | ~ l1_orders_2(A_60655) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_209725,plain,(
    ! [A_62102,D_62103,C_62104,A_62105] :
      ( r1_orders_2(A_62102,D_62103,C_62104)
      | ~ m1_subset_1(D_62103,u1_struct_0(A_62102))
      | ~ r2_lattice3(A_62102,k2_tarski(A_62105,D_62103),C_62104)
      | ~ m1_subset_1(C_62104,u1_struct_0(A_62102))
      | ~ l1_orders_2(A_62102) ) ),
    inference(resolution,[status(thm)],[c_4,c_206993])).

tff(c_209740,plain,
    ( r1_orders_2('#skF_5','#skF_8','#skF_6')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_205251,c_209725])).

tff(c_209743,plain,(
    r1_orders_2('#skF_5','#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_209740])).

tff(c_209745,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_196120,c_209743])).

tff(c_209747,plain,(
    ~ r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_205249])).

tff(c_196119,plain,
    ( r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6')
    | r1_orders_2('#skF_5','#skF_6','#skF_8')
    | r1_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_209761,plain,(
    r1_orders_2('#skF_5','#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_205250,c_209747,c_196119])).

tff(c_209746,plain,(
    r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_205249])).

tff(c_209749,plain,(
    ! [A_62154,B_62155,C_62156] :
      ( r2_hidden('#skF_3'(A_62154,B_62155,C_62156),B_62155)
      | r1_lattice3(A_62154,B_62155,C_62156)
      | ~ m1_subset_1(C_62156,u1_struct_0(A_62154))
      | ~ l1_orders_2(A_62154) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_268186,plain,(
    ! [A_78161,A_78162,B_78163,C_78164] :
      ( '#skF_3'(A_78161,k2_tarski(A_78162,B_78163),C_78164) = B_78163
      | '#skF_3'(A_78161,k2_tarski(A_78162,B_78163),C_78164) = A_78162
      | r1_lattice3(A_78161,k2_tarski(A_78162,B_78163),C_78164)
      | ~ m1_subset_1(C_78164,u1_struct_0(A_78161))
      | ~ l1_orders_2(A_78161) ) ),
    inference(resolution,[status(thm)],[c_209749,c_2])).

tff(c_268203,plain,
    ( '#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') = '#skF_8'
    | '#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') = '#skF_7'
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_268186,c_205250])).

tff(c_269009,plain,
    ( '#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') = '#skF_8'
    | '#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_268203])).

tff(c_269042,plain,(
    '#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_269009])).

tff(c_269049,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_7')
    | r1_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_269042,c_22])).

tff(c_269910,plain,(
    r1_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_209746,c_269049])).

tff(c_269912,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_205250,c_269910])).

tff(c_269913,plain,(
    '#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_269009])).

tff(c_269921,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_8')
    | r1_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_269913,c_22])).

tff(c_270782,plain,(
    r1_lattice3('#skF_5',k2_tarski('#skF_7','#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_209761,c_269921])).

tff(c_270784,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_205250,c_270782])).

%------------------------------------------------------------------------------
