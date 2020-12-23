%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:56 EST 2020

% Result     : Theorem 10.27s
% Output     : CNFRefutation 10.27s
% Verified   : 
% Statistics : Number of formulae       :  138 (1153 expanded)
%              Number of leaves         :   29 ( 390 expanded)
%              Depth                    :   22
%              Number of atoms          :  292 (3180 expanded)
%              Number of equality atoms :   34 ( 356 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > m1_subset_1 > l1_orders_2 > k4_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( r2_lattice3(A,k1_xboole_0,B)
              & r1_lattice3(A,k1_xboole_0,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).

tff(f_87,axiom,(
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

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

tff(f_73,axiom,(
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

tff(c_16,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_40,plain,
    ( ~ r1_lattice3('#skF_5',k1_xboole_0,'#skF_6')
    | ~ r2_lattice3('#skF_5',k1_xboole_0,'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_53,plain,(
    ~ r2_lattice3('#skF_5',k1_xboole_0,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_44,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_147,plain,(
    ! [A_80,B_81,C_82] :
      ( r2_hidden('#skF_4'(A_80,B_81,C_82),B_81)
      | r2_lattice3(A_80,B_81,C_82)
      | ~ m1_subset_1(C_82,u1_struct_0(A_80))
      | ~ l1_orders_2(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_14,plain,(
    ! [C_9,A_6,B_7] :
      ( r2_hidden(C_9,A_6)
      | ~ r2_hidden(C_9,B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3874,plain,(
    ! [A_1608,B_1609,C_1610,A_1611] :
      ( r2_hidden('#skF_4'(A_1608,B_1609,C_1610),A_1611)
      | ~ m1_subset_1(B_1609,k1_zfmisc_1(A_1611))
      | r2_lattice3(A_1608,B_1609,C_1610)
      | ~ m1_subset_1(C_1610,u1_struct_0(A_1608))
      | ~ l1_orders_2(A_1608) ) ),
    inference(resolution,[status(thm)],[c_147,c_14])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5588,plain,(
    ! [A_2691,A_2692,B_2693,C_2694] :
      ( A_2691 = '#skF_4'(A_2692,B_2693,C_2694)
      | ~ m1_subset_1(B_2693,k1_zfmisc_1(k1_tarski(A_2691)))
      | r2_lattice3(A_2692,B_2693,C_2694)
      | ~ m1_subset_1(C_2694,u1_struct_0(A_2692))
      | ~ l1_orders_2(A_2692) ) ),
    inference(resolution,[status(thm)],[c_3874,c_2])).

tff(c_5617,plain,(
    ! [A_2711,A_2712,C_2713] :
      ( A_2711 = '#skF_4'(A_2712,k1_xboole_0,C_2713)
      | r2_lattice3(A_2712,k1_xboole_0,C_2713)
      | ~ m1_subset_1(C_2713,u1_struct_0(A_2712))
      | ~ l1_orders_2(A_2712) ) ),
    inference(resolution,[status(thm)],[c_16,c_5588])).

tff(c_5637,plain,(
    ! [A_2711] :
      ( A_2711 = '#skF_4'('#skF_5',k1_xboole_0,'#skF_6')
      | r2_lattice3('#skF_5',k1_xboole_0,'#skF_6')
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_42,c_5617])).

tff(c_5646,plain,(
    ! [A_2711] :
      ( A_2711 = '#skF_4'('#skF_5',k1_xboole_0,'#skF_6')
      | r2_lattice3('#skF_5',k1_xboole_0,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_5637])).

tff(c_6032,plain,(
    '#skF_4'('#skF_5',k1_xboole_0,'#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_5646])).

tff(c_5648,plain,(
    ! [A_2730] : A_2730 = '#skF_4'('#skF_5',k1_xboole_0,'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_5646])).

tff(c_6594,plain,(
    ! [A_6045] : k1_xboole_0 = A_6045 ),
    inference(superposition,[status(thm),theory(equality)],[c_6032,c_5648])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_59,plain,(
    ! [C_55,A_56,B_57] :
      ( r2_hidden(C_55,A_56)
      | ~ r2_hidden(C_55,B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_62,plain,(
    ! [C_5,A_56] :
      ( r2_hidden(C_5,A_56)
      | ~ m1_subset_1(k1_tarski(C_5),k1_zfmisc_1(A_56)) ) ),
    inference(resolution,[status(thm)],[c_4,c_59])).

tff(c_6768,plain,(
    ! [C_5,A_56] :
      ( r2_hidden(C_5,A_56)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_56)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6594,c_62])).

tff(c_6803,plain,(
    ! [C_5,A_56] : r2_hidden(C_5,A_56) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_6768])).

tff(c_7337,plain,(
    ! [C_5,A_1] : C_5 = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6803,c_2])).

tff(c_34,plain,(
    ! [A_33,B_40,C_41] :
      ( ~ r1_orders_2(A_33,'#skF_4'(A_33,B_40,C_41),C_41)
      | r2_lattice3(A_33,B_40,C_41)
      | ~ m1_subset_1(C_41,u1_struct_0(A_33))
      | ~ l1_orders_2(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_5905,plain,(
    ! [A_2730] :
      ( ~ r1_orders_2('#skF_5',A_2730,'#skF_6')
      | r2_lattice3('#skF_5',k1_xboole_0,'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5648,c_34])).

tff(c_6093,plain,(
    ! [A_2730] :
      ( ~ r1_orders_2('#skF_5',A_2730,'#skF_6')
      | r2_lattice3('#skF_5',k1_xboole_0,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_5905])).

tff(c_8578,plain,(
    ! [A_8779] : ~ r1_orders_2('#skF_5',A_8779,'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_6093])).

tff(c_8893,plain,(
    ! [C_9216,A_9217] : ~ r1_orders_2(C_9216,A_9217,'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_7337,c_8578])).

tff(c_8901,plain,(
    ! [C_9216,A_9217,A_1] : ~ r1_orders_2(C_9216,A_9217,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_7337,c_8893])).

tff(c_6786,plain,(
    ! [C_5] : r2_hidden(C_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6594,c_4])).

tff(c_54,plain,(
    ! [A_50,C_51,B_52] :
      ( m1_subset_1(A_50,C_51)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(C_51))
      | ~ r2_hidden(A_50,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_57,plain,(
    ! [A_50,A_10] :
      ( m1_subset_1(A_50,A_10)
      | ~ r2_hidden(A_50,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_54])).

tff(c_7153,plain,(
    ! [A_50,A_10] : m1_subset_1(A_50,A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6786,c_57])).

tff(c_20,plain,(
    ! [A_14,B_18,C_20] :
      ( r1_orders_2(A_14,B_18,C_20)
      | ~ r2_hidden(k4_tarski(B_18,C_20),u1_orders_2(A_14))
      | ~ m1_subset_1(C_20,u1_struct_0(A_14))
      | ~ m1_subset_1(B_18,u1_struct_0(A_14))
      | ~ l1_orders_2(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_7319,plain,(
    ! [A_14,B_18,C_20] :
      ( r1_orders_2(A_14,B_18,C_20)
      | ~ m1_subset_1(C_20,u1_struct_0(A_14))
      | ~ m1_subset_1(B_18,u1_struct_0(A_14))
      | ~ l1_orders_2(A_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6803,c_20])).

tff(c_9345,plain,(
    ! [A_14,B_18,C_20] :
      ( r1_orders_2(A_14,B_18,C_20)
      | ~ l1_orders_2(A_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7153,c_7153,c_7319])).

tff(c_9346,plain,(
    ! [A_14] : ~ l1_orders_2(A_14) ),
    inference(negUnitSimplification,[status(thm)],[c_8901,c_9345])).

tff(c_6026,plain,(
    '#skF_4'('#skF_5',k1_xboole_0,'#skF_6') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_5646])).

tff(c_6586,plain,(
    '#skF_5' = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_6026,c_5648])).

tff(c_6587,plain,(
    l1_orders_2('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_6586,c_44])).

tff(c_9349,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9346,c_6587])).

tff(c_9350,plain,(
    ~ r1_lattice3('#skF_5',k1_xboole_0,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_9445,plain,(
    ! [A_9525,B_9526,C_9527] :
      ( r2_hidden('#skF_3'(A_9525,B_9526,C_9527),B_9526)
      | r1_lattice3(A_9525,B_9526,C_9527)
      | ~ m1_subset_1(C_9527,u1_struct_0(A_9525))
      | ~ l1_orders_2(A_9525) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_13124,plain,(
    ! [A_11070,B_11071,C_11072,A_11073] :
      ( r2_hidden('#skF_3'(A_11070,B_11071,C_11072),A_11073)
      | ~ m1_subset_1(B_11071,k1_zfmisc_1(A_11073))
      | r1_lattice3(A_11070,B_11071,C_11072)
      | ~ m1_subset_1(C_11072,u1_struct_0(A_11070))
      | ~ l1_orders_2(A_11070) ) ),
    inference(resolution,[status(thm)],[c_9445,c_14])).

tff(c_19988,plain,(
    ! [A_18645,A_18646,B_18647,C_18648] :
      ( A_18645 = '#skF_3'(A_18646,B_18647,C_18648)
      | ~ m1_subset_1(B_18647,k1_zfmisc_1(k1_tarski(A_18645)))
      | r1_lattice3(A_18646,B_18647,C_18648)
      | ~ m1_subset_1(C_18648,u1_struct_0(A_18646))
      | ~ l1_orders_2(A_18646) ) ),
    inference(resolution,[status(thm)],[c_13124,c_2])).

tff(c_20019,plain,(
    ! [A_18649,A_18650,C_18651] :
      ( A_18649 = '#skF_3'(A_18650,k1_xboole_0,C_18651)
      | r1_lattice3(A_18650,k1_xboole_0,C_18651)
      | ~ m1_subset_1(C_18651,u1_struct_0(A_18650))
      | ~ l1_orders_2(A_18650) ) ),
    inference(resolution,[status(thm)],[c_16,c_19988])).

tff(c_20043,plain,(
    ! [A_18649] :
      ( A_18649 = '#skF_3'('#skF_5',k1_xboole_0,'#skF_6')
      | r1_lattice3('#skF_5',k1_xboole_0,'#skF_6')
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_42,c_20019])).

tff(c_20054,plain,(
    ! [A_18649] :
      ( A_18649 = '#skF_3'('#skF_5',k1_xboole_0,'#skF_6')
      | r1_lattice3('#skF_5',k1_xboole_0,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_20043])).

tff(c_20056,plain,(
    ! [A_18652] : A_18652 = '#skF_3'('#skF_5',k1_xboole_0,'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_9350,c_20054])).

tff(c_26,plain,(
    ! [A_21,C_29,B_28] :
      ( ~ r1_orders_2(A_21,C_29,'#skF_3'(A_21,B_28,C_29))
      | r1_lattice3(A_21,B_28,C_29)
      | ~ m1_subset_1(C_29,u1_struct_0(A_21))
      | ~ l1_orders_2(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_20383,plain,(
    ! [A_18652] :
      ( ~ r1_orders_2('#skF_5','#skF_6',A_18652)
      | r1_lattice3('#skF_5',k1_xboole_0,'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20056,c_26])).

tff(c_20546,plain,(
    ! [A_18652] :
      ( ~ r1_orders_2('#skF_5','#skF_6',A_18652)
      | r1_lattice3('#skF_5',k1_xboole_0,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_20383])).

tff(c_20547,plain,(
    ! [A_18652] : ~ r1_orders_2('#skF_5','#skF_6',A_18652) ),
    inference(negUnitSimplification,[status(thm)],[c_9350,c_20546])).

tff(c_15489,plain,(
    ! [A_12267,A_12268,B_12269,C_12270] :
      ( A_12267 = '#skF_3'(A_12268,B_12269,C_12270)
      | ~ m1_subset_1(B_12269,k1_zfmisc_1(k1_tarski(A_12267)))
      | r1_lattice3(A_12268,B_12269,C_12270)
      | ~ m1_subset_1(C_12270,u1_struct_0(A_12268))
      | ~ l1_orders_2(A_12268) ) ),
    inference(resolution,[status(thm)],[c_13124,c_2])).

tff(c_15562,plain,(
    ! [A_12272,A_12273,C_12274] :
      ( A_12272 = '#skF_3'(A_12273,k1_xboole_0,C_12274)
      | r1_lattice3(A_12273,k1_xboole_0,C_12274)
      | ~ m1_subset_1(C_12274,u1_struct_0(A_12273))
      | ~ l1_orders_2(A_12273) ) ),
    inference(resolution,[status(thm)],[c_16,c_15489])).

tff(c_15586,plain,(
    ! [A_12272] :
      ( A_12272 = '#skF_3'('#skF_5',k1_xboole_0,'#skF_6')
      | r1_lattice3('#skF_5',k1_xboole_0,'#skF_6')
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_42,c_15562])).

tff(c_15597,plain,(
    ! [A_12272] :
      ( A_12272 = '#skF_3'('#skF_5',k1_xboole_0,'#skF_6')
      | r1_lattice3('#skF_5',k1_xboole_0,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_15586])).

tff(c_15606,plain,(
    '#skF_3'('#skF_5',k1_xboole_0,'#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_9350,c_15597])).

tff(c_15598,plain,(
    ! [A_12272] : A_12272 = '#skF_3'('#skF_5',k1_xboole_0,'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_9350,c_15597])).

tff(c_16364,plain,(
    ! [A_14709] : k1_xboole_0 = A_14709 ),
    inference(superposition,[status(thm),theory(equality)],[c_15606,c_15598])).

tff(c_9428,plain,(
    ! [A_9522,B_9523,C_9524] :
      ( r2_hidden('#skF_4'(A_9522,B_9523,C_9524),B_9523)
      | r2_lattice3(A_9522,B_9523,C_9524)
      | ~ m1_subset_1(C_9524,u1_struct_0(A_9522))
      | ~ l1_orders_2(A_9522) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_9444,plain,(
    ! [A_9522,A_1,C_9524] :
      ( '#skF_4'(A_9522,k1_tarski(A_1),C_9524) = A_1
      | r2_lattice3(A_9522,k1_tarski(A_1),C_9524)
      | ~ m1_subset_1(C_9524,u1_struct_0(A_9522))
      | ~ l1_orders_2(A_9522) ) ),
    inference(resolution,[status(thm)],[c_9428,c_2])).

tff(c_12976,plain,(
    ! [A_11045,D_11046,C_11047,B_11048] :
      ( r1_orders_2(A_11045,D_11046,C_11047)
      | ~ r2_hidden(D_11046,B_11048)
      | ~ m1_subset_1(D_11046,u1_struct_0(A_11045))
      | ~ r2_lattice3(A_11045,B_11048,C_11047)
      | ~ m1_subset_1(C_11047,u1_struct_0(A_11045))
      | ~ l1_orders_2(A_11045) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_13111,plain,(
    ! [A_11067,C_11068,C_11069] :
      ( r1_orders_2(A_11067,C_11068,C_11069)
      | ~ m1_subset_1(C_11068,u1_struct_0(A_11067))
      | ~ r2_lattice3(A_11067,k1_tarski(C_11068),C_11069)
      | ~ m1_subset_1(C_11069,u1_struct_0(A_11067))
      | ~ l1_orders_2(A_11067) ) ),
    inference(resolution,[status(thm)],[c_4,c_12976])).

tff(c_15173,plain,(
    ! [A_12254,A_12255,C_12256] :
      ( r1_orders_2(A_12254,A_12255,C_12256)
      | ~ m1_subset_1(A_12255,u1_struct_0(A_12254))
      | '#skF_4'(A_12254,k1_tarski(A_12255),C_12256) = A_12255
      | ~ m1_subset_1(C_12256,u1_struct_0(A_12254))
      | ~ l1_orders_2(A_12254) ) ),
    inference(resolution,[status(thm)],[c_9444,c_13111])).

tff(c_15194,plain,(
    ! [C_12256] :
      ( r1_orders_2('#skF_5','#skF_6',C_12256)
      | '#skF_4'('#skF_5',k1_tarski('#skF_6'),C_12256) = '#skF_6'
      | ~ m1_subset_1(C_12256,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_42,c_15173])).

tff(c_15205,plain,(
    ! [C_12257] :
      ( r1_orders_2('#skF_5','#skF_6',C_12257)
      | '#skF_4'('#skF_5',k1_tarski('#skF_6'),C_12257) = '#skF_6'
      | ~ m1_subset_1(C_12257,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_15194])).

tff(c_15248,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_6')
    | '#skF_4'('#skF_5',k1_tarski('#skF_6'),'#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_42,c_15205])).

tff(c_15249,plain,(
    '#skF_4'('#skF_5',k1_tarski('#skF_6'),'#skF_6') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_15248])).

tff(c_13161,plain,(
    ! [A_11074,B_11075,C_11076,A_11077] :
      ( r2_hidden('#skF_4'(A_11074,B_11075,C_11076),A_11077)
      | ~ m1_subset_1(B_11075,k1_zfmisc_1(A_11077))
      | r2_lattice3(A_11074,B_11075,C_11076)
      | ~ m1_subset_1(C_11076,u1_struct_0(A_11074))
      | ~ l1_orders_2(A_11074) ) ),
    inference(resolution,[status(thm)],[c_9428,c_14])).

tff(c_9357,plain,(
    ! [A_9500,C_9501,B_9502] :
      ( m1_subset_1(A_9500,C_9501)
      | ~ m1_subset_1(B_9502,k1_zfmisc_1(C_9501))
      | ~ r2_hidden(A_9500,B_9502) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_9360,plain,(
    ! [A_9500,A_10] :
      ( m1_subset_1(A_9500,A_10)
      | ~ r2_hidden(A_9500,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_9357])).

tff(c_15320,plain,(
    ! [A_12259,B_12260,C_12261,A_12262] :
      ( m1_subset_1('#skF_4'(A_12259,B_12260,C_12261),A_12262)
      | ~ m1_subset_1(B_12260,k1_zfmisc_1(k1_xboole_0))
      | r2_lattice3(A_12259,B_12260,C_12261)
      | ~ m1_subset_1(C_12261,u1_struct_0(A_12259))
      | ~ l1_orders_2(A_12259) ) ),
    inference(resolution,[status(thm)],[c_13161,c_9360])).

tff(c_15351,plain,(
    ! [A_12262] :
      ( m1_subset_1('#skF_6',A_12262)
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(k1_xboole_0))
      | r2_lattice3('#skF_5',k1_tarski('#skF_6'),'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15249,c_15320])).

tff(c_15363,plain,(
    ! [A_12262] :
      ( m1_subset_1('#skF_6',A_12262)
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(k1_xboole_0))
      | r2_lattice3('#skF_5',k1_tarski('#skF_6'),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_15351])).

tff(c_15364,plain,(
    ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_15363])).

tff(c_16392,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16364,c_15364])).

tff(c_16598,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16392])).

tff(c_16600,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_15363])).

tff(c_9352,plain,(
    ! [C_9495,A_9496,B_9497] :
      ( r2_hidden(C_9495,A_9496)
      | ~ r2_hidden(C_9495,B_9497)
      | ~ m1_subset_1(B_9497,k1_zfmisc_1(A_9496)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_9355,plain,(
    ! [C_5,A_9496] :
      ( r2_hidden(C_5,A_9496)
      | ~ m1_subset_1(k1_tarski(C_5),k1_zfmisc_1(A_9496)) ) ),
    inference(resolution,[status(thm)],[c_4,c_9352])).

tff(c_16607,plain,(
    r2_hidden('#skF_6',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16600,c_9355])).

tff(c_16661,plain,(
    ! [A_10] : m1_subset_1('#skF_6',A_10) ),
    inference(resolution,[status(thm)],[c_16607,c_9360])).

tff(c_16656,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_6',A_6)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ) ),
    inference(resolution,[status(thm)],[c_16607,c_14])).

tff(c_16699,plain,(
    ! [A_15834] : r2_hidden('#skF_6',A_15834) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16656])).

tff(c_16805,plain,(
    ! [A_15836] : A_15836 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_16699,c_2])).

tff(c_16987,plain,(
    ! [C_5,A_9496] :
      ( r2_hidden(C_5,A_9496)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_9496)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16805,c_9355])).

tff(c_17058,plain,(
    ! [C_5,A_9496] : r2_hidden(C_5,A_9496) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16661,c_16987])).

tff(c_17113,plain,(
    ! [C_5,A_1] : C_5 = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_17058,c_2])).

tff(c_18964,plain,(
    ! [A_17971] : ~ r1_lattice3('#skF_5',k1_xboole_0,A_17971) ),
    inference(superposition,[status(thm),theory(equality)],[c_16805,c_9350])).

tff(c_18972,plain,(
    ! [A_1,A_17971] : ~ r1_lattice3('#skF_5',A_1,A_17971) ),
    inference(superposition,[status(thm),theory(equality)],[c_17113,c_18964])).

tff(c_17106,plain,(
    ! [A_9500,A_10] : m1_subset_1(A_9500,A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17058,c_9360])).

tff(c_30,plain,(
    ! [A_21,B_28,C_29] :
      ( m1_subset_1('#skF_3'(A_21,B_28,C_29),u1_struct_0(A_21))
      | r1_lattice3(A_21,B_28,C_29)
      | ~ m1_subset_1(C_29,u1_struct_0(A_21))
      | ~ l1_orders_2(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_28,plain,(
    ! [A_21,B_28,C_29] :
      ( r2_hidden('#skF_3'(A_21,B_28,C_29),B_28)
      | r1_lattice3(A_21,B_28,C_29)
      | ~ m1_subset_1(C_29,u1_struct_0(A_21))
      | ~ l1_orders_2(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_14822,plain,(
    ! [B_12095,A_12093,A_12096,C_12094,C_12092] :
      ( r1_orders_2(A_12096,'#skF_3'(A_12093,B_12095,C_12092),C_12094)
      | ~ m1_subset_1('#skF_3'(A_12093,B_12095,C_12092),u1_struct_0(A_12096))
      | ~ r2_lattice3(A_12096,B_12095,C_12094)
      | ~ m1_subset_1(C_12094,u1_struct_0(A_12096))
      | ~ l1_orders_2(A_12096)
      | r1_lattice3(A_12093,B_12095,C_12092)
      | ~ m1_subset_1(C_12092,u1_struct_0(A_12093))
      | ~ l1_orders_2(A_12093) ) ),
    inference(resolution,[status(thm)],[c_28,c_12976])).

tff(c_14833,plain,(
    ! [A_21,B_28,C_29,C_12094] :
      ( r1_orders_2(A_21,'#skF_3'(A_21,B_28,C_29),C_12094)
      | ~ r2_lattice3(A_21,B_28,C_12094)
      | ~ m1_subset_1(C_12094,u1_struct_0(A_21))
      | r1_lattice3(A_21,B_28,C_29)
      | ~ m1_subset_1(C_29,u1_struct_0(A_21))
      | ~ l1_orders_2(A_21) ) ),
    inference(resolution,[status(thm)],[c_30,c_14822])).

tff(c_19224,plain,(
    ! [A_18397,B_18398,C_18399,C_18400] :
      ( r1_orders_2(A_18397,'#skF_3'(A_18397,B_18398,C_18399),C_18400)
      | ~ r2_lattice3(A_18397,B_18398,C_18400)
      | r1_lattice3(A_18397,B_18398,C_18399)
      | ~ l1_orders_2(A_18397) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17106,c_17106,c_14833])).

tff(c_15263,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_6')
    | r2_lattice3('#skF_5',k1_tarski('#skF_6'),'#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_15249,c_34])).

tff(c_15278,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_6')
    | r2_lattice3('#skF_5',k1_tarski('#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_15263])).

tff(c_15319,plain,(
    ~ r1_orders_2('#skF_5','#skF_6','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_15278])).

tff(c_16816,plain,(
    ! [A_15836] : ~ r1_orders_2('#skF_5',A_15836,'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_16805,c_15319])).

tff(c_19228,plain,(
    ! [B_18398,C_18399] :
      ( ~ r2_lattice3('#skF_5',B_18398,'#skF_6')
      | r1_lattice3('#skF_5',B_18398,C_18399)
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_19224,c_16816])).

tff(c_19327,plain,(
    ! [B_18398,C_18399] :
      ( ~ r2_lattice3('#skF_5',B_18398,'#skF_6')
      | r1_lattice3('#skF_5',B_18398,C_18399) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_19228])).

tff(c_19328,plain,(
    ! [B_18398] : ~ r2_lattice3('#skF_5',B_18398,'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_18972,c_19327])).

tff(c_18541,plain,(
    ! [C_17007] : C_17007 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17058,c_2])).

tff(c_9351,plain,(
    r2_lattice3('#skF_5',k1_xboole_0,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_18543,plain,(
    r2_lattice3('#skF_5','#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_18541,c_9351])).

tff(c_19874,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19328,c_18543])).

tff(c_19876,plain,(
    r1_orders_2('#skF_5','#skF_6','#skF_6') ),
    inference(splitRight,[status(thm)],[c_15278])).

tff(c_24100,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20547,c_19876])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:33:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.27/3.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.27/3.37  
% 10.27/3.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.27/3.37  %$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > m1_subset_1 > l1_orders_2 > k4_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1
% 10.27/3.37  
% 10.27/3.37  %Foreground sorts:
% 10.27/3.37  
% 10.27/3.37  
% 10.27/3.37  %Background operators:
% 10.27/3.37  
% 10.27/3.37  
% 10.27/3.37  %Foreground operators:
% 10.27/3.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.27/3.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.27/3.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.27/3.37  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 10.27/3.37  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 10.27/3.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.27/3.37  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 10.27/3.37  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 10.27/3.37  tff('#skF_5', type, '#skF_5': $i).
% 10.27/3.37  tff('#skF_6', type, '#skF_6': $i).
% 10.27/3.37  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 10.27/3.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.27/3.37  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 10.27/3.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.27/3.37  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 10.27/3.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.27/3.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.27/3.37  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 10.27/3.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.27/3.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.27/3.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.27/3.37  
% 10.27/3.39  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 10.27/3.39  tff(f_97, negated_conjecture, ~(![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (r2_lattice3(A, k1_xboole_0, B) & r1_lattice3(A, k1_xboole_0, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_yellow_0)).
% 10.27/3.39  tff(f_87, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, D, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattice3)).
% 10.27/3.39  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 10.27/3.39  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 10.27/3.39  tff(f_47, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 10.27/3.39  tff(f_59, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_orders_2(A, B, C) <=> r2_hidden(k4_tarski(B, C), u1_orders_2(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_orders_2)).
% 10.27/3.39  tff(f_73, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, C, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_lattice3)).
% 10.27/3.39  tff(c_16, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.27/3.39  tff(c_40, plain, (~r1_lattice3('#skF_5', k1_xboole_0, '#skF_6') | ~r2_lattice3('#skF_5', k1_xboole_0, '#skF_6')), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.27/3.39  tff(c_53, plain, (~r2_lattice3('#skF_5', k1_xboole_0, '#skF_6')), inference(splitLeft, [status(thm)], [c_40])).
% 10.27/3.39  tff(c_44, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.27/3.39  tff(c_42, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.27/3.39  tff(c_147, plain, (![A_80, B_81, C_82]: (r2_hidden('#skF_4'(A_80, B_81, C_82), B_81) | r2_lattice3(A_80, B_81, C_82) | ~m1_subset_1(C_82, u1_struct_0(A_80)) | ~l1_orders_2(A_80))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.27/3.39  tff(c_14, plain, (![C_9, A_6, B_7]: (r2_hidden(C_9, A_6) | ~r2_hidden(C_9, B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.27/3.39  tff(c_3874, plain, (![A_1608, B_1609, C_1610, A_1611]: (r2_hidden('#skF_4'(A_1608, B_1609, C_1610), A_1611) | ~m1_subset_1(B_1609, k1_zfmisc_1(A_1611)) | r2_lattice3(A_1608, B_1609, C_1610) | ~m1_subset_1(C_1610, u1_struct_0(A_1608)) | ~l1_orders_2(A_1608))), inference(resolution, [status(thm)], [c_147, c_14])).
% 10.27/3.39  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.27/3.39  tff(c_5588, plain, (![A_2691, A_2692, B_2693, C_2694]: (A_2691='#skF_4'(A_2692, B_2693, C_2694) | ~m1_subset_1(B_2693, k1_zfmisc_1(k1_tarski(A_2691))) | r2_lattice3(A_2692, B_2693, C_2694) | ~m1_subset_1(C_2694, u1_struct_0(A_2692)) | ~l1_orders_2(A_2692))), inference(resolution, [status(thm)], [c_3874, c_2])).
% 10.27/3.39  tff(c_5617, plain, (![A_2711, A_2712, C_2713]: (A_2711='#skF_4'(A_2712, k1_xboole_0, C_2713) | r2_lattice3(A_2712, k1_xboole_0, C_2713) | ~m1_subset_1(C_2713, u1_struct_0(A_2712)) | ~l1_orders_2(A_2712))), inference(resolution, [status(thm)], [c_16, c_5588])).
% 10.27/3.39  tff(c_5637, plain, (![A_2711]: (A_2711='#skF_4'('#skF_5', k1_xboole_0, '#skF_6') | r2_lattice3('#skF_5', k1_xboole_0, '#skF_6') | ~l1_orders_2('#skF_5'))), inference(resolution, [status(thm)], [c_42, c_5617])).
% 10.27/3.39  tff(c_5646, plain, (![A_2711]: (A_2711='#skF_4'('#skF_5', k1_xboole_0, '#skF_6') | r2_lattice3('#skF_5', k1_xboole_0, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_5637])).
% 10.27/3.39  tff(c_6032, plain, ('#skF_4'('#skF_5', k1_xboole_0, '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_53, c_5646])).
% 10.27/3.39  tff(c_5648, plain, (![A_2730]: (A_2730='#skF_4'('#skF_5', k1_xboole_0, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_53, c_5646])).
% 10.27/3.39  tff(c_6594, plain, (![A_6045]: (k1_xboole_0=A_6045)), inference(superposition, [status(thm), theory('equality')], [c_6032, c_5648])).
% 10.27/3.39  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.27/3.39  tff(c_59, plain, (![C_55, A_56, B_57]: (r2_hidden(C_55, A_56) | ~r2_hidden(C_55, B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.27/3.39  tff(c_62, plain, (![C_5, A_56]: (r2_hidden(C_5, A_56) | ~m1_subset_1(k1_tarski(C_5), k1_zfmisc_1(A_56)))), inference(resolution, [status(thm)], [c_4, c_59])).
% 10.27/3.39  tff(c_6768, plain, (![C_5, A_56]: (r2_hidden(C_5, A_56) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_56)))), inference(superposition, [status(thm), theory('equality')], [c_6594, c_62])).
% 10.27/3.39  tff(c_6803, plain, (![C_5, A_56]: (r2_hidden(C_5, A_56))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_6768])).
% 10.27/3.39  tff(c_7337, plain, (![C_5, A_1]: (C_5=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_6803, c_2])).
% 10.27/3.39  tff(c_34, plain, (![A_33, B_40, C_41]: (~r1_orders_2(A_33, '#skF_4'(A_33, B_40, C_41), C_41) | r2_lattice3(A_33, B_40, C_41) | ~m1_subset_1(C_41, u1_struct_0(A_33)) | ~l1_orders_2(A_33))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.27/3.39  tff(c_5905, plain, (![A_2730]: (~r1_orders_2('#skF_5', A_2730, '#skF_6') | r2_lattice3('#skF_5', k1_xboole_0, '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5648, c_34])).
% 10.27/3.39  tff(c_6093, plain, (![A_2730]: (~r1_orders_2('#skF_5', A_2730, '#skF_6') | r2_lattice3('#skF_5', k1_xboole_0, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_5905])).
% 10.27/3.39  tff(c_8578, plain, (![A_8779]: (~r1_orders_2('#skF_5', A_8779, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_53, c_6093])).
% 10.27/3.39  tff(c_8893, plain, (![C_9216, A_9217]: (~r1_orders_2(C_9216, A_9217, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_7337, c_8578])).
% 10.27/3.39  tff(c_8901, plain, (![C_9216, A_9217, A_1]: (~r1_orders_2(C_9216, A_9217, A_1))), inference(superposition, [status(thm), theory('equality')], [c_7337, c_8893])).
% 10.27/3.39  tff(c_6786, plain, (![C_5]: (r2_hidden(C_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6594, c_4])).
% 10.27/3.39  tff(c_54, plain, (![A_50, C_51, B_52]: (m1_subset_1(A_50, C_51) | ~m1_subset_1(B_52, k1_zfmisc_1(C_51)) | ~r2_hidden(A_50, B_52))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.27/3.39  tff(c_57, plain, (![A_50, A_10]: (m1_subset_1(A_50, A_10) | ~r2_hidden(A_50, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_54])).
% 10.27/3.39  tff(c_7153, plain, (![A_50, A_10]: (m1_subset_1(A_50, A_10))), inference(demodulation, [status(thm), theory('equality')], [c_6786, c_57])).
% 10.27/3.39  tff(c_20, plain, (![A_14, B_18, C_20]: (r1_orders_2(A_14, B_18, C_20) | ~r2_hidden(k4_tarski(B_18, C_20), u1_orders_2(A_14)) | ~m1_subset_1(C_20, u1_struct_0(A_14)) | ~m1_subset_1(B_18, u1_struct_0(A_14)) | ~l1_orders_2(A_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.27/3.39  tff(c_7319, plain, (![A_14, B_18, C_20]: (r1_orders_2(A_14, B_18, C_20) | ~m1_subset_1(C_20, u1_struct_0(A_14)) | ~m1_subset_1(B_18, u1_struct_0(A_14)) | ~l1_orders_2(A_14))), inference(demodulation, [status(thm), theory('equality')], [c_6803, c_20])).
% 10.27/3.39  tff(c_9345, plain, (![A_14, B_18, C_20]: (r1_orders_2(A_14, B_18, C_20) | ~l1_orders_2(A_14))), inference(demodulation, [status(thm), theory('equality')], [c_7153, c_7153, c_7319])).
% 10.27/3.39  tff(c_9346, plain, (![A_14]: (~l1_orders_2(A_14))), inference(negUnitSimplification, [status(thm)], [c_8901, c_9345])).
% 10.27/3.39  tff(c_6026, plain, ('#skF_4'('#skF_5', k1_xboole_0, '#skF_6')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_53, c_5646])).
% 10.27/3.39  tff(c_6586, plain, ('#skF_5'='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_6026, c_5648])).
% 10.27/3.39  tff(c_6587, plain, (l1_orders_2('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_6586, c_44])).
% 10.27/3.39  tff(c_9349, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9346, c_6587])).
% 10.27/3.39  tff(c_9350, plain, (~r1_lattice3('#skF_5', k1_xboole_0, '#skF_6')), inference(splitRight, [status(thm)], [c_40])).
% 10.27/3.39  tff(c_9445, plain, (![A_9525, B_9526, C_9527]: (r2_hidden('#skF_3'(A_9525, B_9526, C_9527), B_9526) | r1_lattice3(A_9525, B_9526, C_9527) | ~m1_subset_1(C_9527, u1_struct_0(A_9525)) | ~l1_orders_2(A_9525))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.27/3.39  tff(c_13124, plain, (![A_11070, B_11071, C_11072, A_11073]: (r2_hidden('#skF_3'(A_11070, B_11071, C_11072), A_11073) | ~m1_subset_1(B_11071, k1_zfmisc_1(A_11073)) | r1_lattice3(A_11070, B_11071, C_11072) | ~m1_subset_1(C_11072, u1_struct_0(A_11070)) | ~l1_orders_2(A_11070))), inference(resolution, [status(thm)], [c_9445, c_14])).
% 10.27/3.39  tff(c_19988, plain, (![A_18645, A_18646, B_18647, C_18648]: (A_18645='#skF_3'(A_18646, B_18647, C_18648) | ~m1_subset_1(B_18647, k1_zfmisc_1(k1_tarski(A_18645))) | r1_lattice3(A_18646, B_18647, C_18648) | ~m1_subset_1(C_18648, u1_struct_0(A_18646)) | ~l1_orders_2(A_18646))), inference(resolution, [status(thm)], [c_13124, c_2])).
% 10.27/3.39  tff(c_20019, plain, (![A_18649, A_18650, C_18651]: (A_18649='#skF_3'(A_18650, k1_xboole_0, C_18651) | r1_lattice3(A_18650, k1_xboole_0, C_18651) | ~m1_subset_1(C_18651, u1_struct_0(A_18650)) | ~l1_orders_2(A_18650))), inference(resolution, [status(thm)], [c_16, c_19988])).
% 10.27/3.39  tff(c_20043, plain, (![A_18649]: (A_18649='#skF_3'('#skF_5', k1_xboole_0, '#skF_6') | r1_lattice3('#skF_5', k1_xboole_0, '#skF_6') | ~l1_orders_2('#skF_5'))), inference(resolution, [status(thm)], [c_42, c_20019])).
% 10.27/3.39  tff(c_20054, plain, (![A_18649]: (A_18649='#skF_3'('#skF_5', k1_xboole_0, '#skF_6') | r1_lattice3('#skF_5', k1_xboole_0, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_20043])).
% 10.27/3.39  tff(c_20056, plain, (![A_18652]: (A_18652='#skF_3'('#skF_5', k1_xboole_0, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_9350, c_20054])).
% 10.27/3.39  tff(c_26, plain, (![A_21, C_29, B_28]: (~r1_orders_2(A_21, C_29, '#skF_3'(A_21, B_28, C_29)) | r1_lattice3(A_21, B_28, C_29) | ~m1_subset_1(C_29, u1_struct_0(A_21)) | ~l1_orders_2(A_21))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.27/3.39  tff(c_20383, plain, (![A_18652]: (~r1_orders_2('#skF_5', '#skF_6', A_18652) | r1_lattice3('#skF_5', k1_xboole_0, '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_20056, c_26])).
% 10.27/3.39  tff(c_20546, plain, (![A_18652]: (~r1_orders_2('#skF_5', '#skF_6', A_18652) | r1_lattice3('#skF_5', k1_xboole_0, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_20383])).
% 10.27/3.39  tff(c_20547, plain, (![A_18652]: (~r1_orders_2('#skF_5', '#skF_6', A_18652))), inference(negUnitSimplification, [status(thm)], [c_9350, c_20546])).
% 10.27/3.39  tff(c_15489, plain, (![A_12267, A_12268, B_12269, C_12270]: (A_12267='#skF_3'(A_12268, B_12269, C_12270) | ~m1_subset_1(B_12269, k1_zfmisc_1(k1_tarski(A_12267))) | r1_lattice3(A_12268, B_12269, C_12270) | ~m1_subset_1(C_12270, u1_struct_0(A_12268)) | ~l1_orders_2(A_12268))), inference(resolution, [status(thm)], [c_13124, c_2])).
% 10.27/3.39  tff(c_15562, plain, (![A_12272, A_12273, C_12274]: (A_12272='#skF_3'(A_12273, k1_xboole_0, C_12274) | r1_lattice3(A_12273, k1_xboole_0, C_12274) | ~m1_subset_1(C_12274, u1_struct_0(A_12273)) | ~l1_orders_2(A_12273))), inference(resolution, [status(thm)], [c_16, c_15489])).
% 10.27/3.39  tff(c_15586, plain, (![A_12272]: (A_12272='#skF_3'('#skF_5', k1_xboole_0, '#skF_6') | r1_lattice3('#skF_5', k1_xboole_0, '#skF_6') | ~l1_orders_2('#skF_5'))), inference(resolution, [status(thm)], [c_42, c_15562])).
% 10.27/3.39  tff(c_15597, plain, (![A_12272]: (A_12272='#skF_3'('#skF_5', k1_xboole_0, '#skF_6') | r1_lattice3('#skF_5', k1_xboole_0, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_15586])).
% 10.27/3.39  tff(c_15606, plain, ('#skF_3'('#skF_5', k1_xboole_0, '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_9350, c_15597])).
% 10.27/3.39  tff(c_15598, plain, (![A_12272]: (A_12272='#skF_3'('#skF_5', k1_xboole_0, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_9350, c_15597])).
% 10.27/3.39  tff(c_16364, plain, (![A_14709]: (k1_xboole_0=A_14709)), inference(superposition, [status(thm), theory('equality')], [c_15606, c_15598])).
% 10.27/3.39  tff(c_9428, plain, (![A_9522, B_9523, C_9524]: (r2_hidden('#skF_4'(A_9522, B_9523, C_9524), B_9523) | r2_lattice3(A_9522, B_9523, C_9524) | ~m1_subset_1(C_9524, u1_struct_0(A_9522)) | ~l1_orders_2(A_9522))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.27/3.39  tff(c_9444, plain, (![A_9522, A_1, C_9524]: ('#skF_4'(A_9522, k1_tarski(A_1), C_9524)=A_1 | r2_lattice3(A_9522, k1_tarski(A_1), C_9524) | ~m1_subset_1(C_9524, u1_struct_0(A_9522)) | ~l1_orders_2(A_9522))), inference(resolution, [status(thm)], [c_9428, c_2])).
% 10.27/3.39  tff(c_12976, plain, (![A_11045, D_11046, C_11047, B_11048]: (r1_orders_2(A_11045, D_11046, C_11047) | ~r2_hidden(D_11046, B_11048) | ~m1_subset_1(D_11046, u1_struct_0(A_11045)) | ~r2_lattice3(A_11045, B_11048, C_11047) | ~m1_subset_1(C_11047, u1_struct_0(A_11045)) | ~l1_orders_2(A_11045))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.27/3.39  tff(c_13111, plain, (![A_11067, C_11068, C_11069]: (r1_orders_2(A_11067, C_11068, C_11069) | ~m1_subset_1(C_11068, u1_struct_0(A_11067)) | ~r2_lattice3(A_11067, k1_tarski(C_11068), C_11069) | ~m1_subset_1(C_11069, u1_struct_0(A_11067)) | ~l1_orders_2(A_11067))), inference(resolution, [status(thm)], [c_4, c_12976])).
% 10.27/3.39  tff(c_15173, plain, (![A_12254, A_12255, C_12256]: (r1_orders_2(A_12254, A_12255, C_12256) | ~m1_subset_1(A_12255, u1_struct_0(A_12254)) | '#skF_4'(A_12254, k1_tarski(A_12255), C_12256)=A_12255 | ~m1_subset_1(C_12256, u1_struct_0(A_12254)) | ~l1_orders_2(A_12254))), inference(resolution, [status(thm)], [c_9444, c_13111])).
% 10.27/3.39  tff(c_15194, plain, (![C_12256]: (r1_orders_2('#skF_5', '#skF_6', C_12256) | '#skF_4'('#skF_5', k1_tarski('#skF_6'), C_12256)='#skF_6' | ~m1_subset_1(C_12256, u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5'))), inference(resolution, [status(thm)], [c_42, c_15173])).
% 10.27/3.39  tff(c_15205, plain, (![C_12257]: (r1_orders_2('#skF_5', '#skF_6', C_12257) | '#skF_4'('#skF_5', k1_tarski('#skF_6'), C_12257)='#skF_6' | ~m1_subset_1(C_12257, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_15194])).
% 10.27/3.39  tff(c_15248, plain, (r1_orders_2('#skF_5', '#skF_6', '#skF_6') | '#skF_4'('#skF_5', k1_tarski('#skF_6'), '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_42, c_15205])).
% 10.27/3.39  tff(c_15249, plain, ('#skF_4'('#skF_5', k1_tarski('#skF_6'), '#skF_6')='#skF_6'), inference(splitLeft, [status(thm)], [c_15248])).
% 10.27/3.39  tff(c_13161, plain, (![A_11074, B_11075, C_11076, A_11077]: (r2_hidden('#skF_4'(A_11074, B_11075, C_11076), A_11077) | ~m1_subset_1(B_11075, k1_zfmisc_1(A_11077)) | r2_lattice3(A_11074, B_11075, C_11076) | ~m1_subset_1(C_11076, u1_struct_0(A_11074)) | ~l1_orders_2(A_11074))), inference(resolution, [status(thm)], [c_9428, c_14])).
% 10.27/3.39  tff(c_9357, plain, (![A_9500, C_9501, B_9502]: (m1_subset_1(A_9500, C_9501) | ~m1_subset_1(B_9502, k1_zfmisc_1(C_9501)) | ~r2_hidden(A_9500, B_9502))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.27/3.39  tff(c_9360, plain, (![A_9500, A_10]: (m1_subset_1(A_9500, A_10) | ~r2_hidden(A_9500, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_9357])).
% 10.27/3.39  tff(c_15320, plain, (![A_12259, B_12260, C_12261, A_12262]: (m1_subset_1('#skF_4'(A_12259, B_12260, C_12261), A_12262) | ~m1_subset_1(B_12260, k1_zfmisc_1(k1_xboole_0)) | r2_lattice3(A_12259, B_12260, C_12261) | ~m1_subset_1(C_12261, u1_struct_0(A_12259)) | ~l1_orders_2(A_12259))), inference(resolution, [status(thm)], [c_13161, c_9360])).
% 10.27/3.39  tff(c_15351, plain, (![A_12262]: (m1_subset_1('#skF_6', A_12262) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(k1_xboole_0)) | r2_lattice3('#skF_5', k1_tarski('#skF_6'), '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_15249, c_15320])).
% 10.27/3.39  tff(c_15363, plain, (![A_12262]: (m1_subset_1('#skF_6', A_12262) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(k1_xboole_0)) | r2_lattice3('#skF_5', k1_tarski('#skF_6'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_15351])).
% 10.27/3.39  tff(c_15364, plain, (~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_15363])).
% 10.27/3.39  tff(c_16392, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16364, c_15364])).
% 10.27/3.39  tff(c_16598, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_16392])).
% 10.27/3.39  tff(c_16600, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_15363])).
% 10.27/3.39  tff(c_9352, plain, (![C_9495, A_9496, B_9497]: (r2_hidden(C_9495, A_9496) | ~r2_hidden(C_9495, B_9497) | ~m1_subset_1(B_9497, k1_zfmisc_1(A_9496)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.27/3.39  tff(c_9355, plain, (![C_5, A_9496]: (r2_hidden(C_5, A_9496) | ~m1_subset_1(k1_tarski(C_5), k1_zfmisc_1(A_9496)))), inference(resolution, [status(thm)], [c_4, c_9352])).
% 10.27/3.39  tff(c_16607, plain, (r2_hidden('#skF_6', k1_xboole_0)), inference(resolution, [status(thm)], [c_16600, c_9355])).
% 10.27/3.39  tff(c_16661, plain, (![A_10]: (m1_subset_1('#skF_6', A_10))), inference(resolution, [status(thm)], [c_16607, c_9360])).
% 10.27/3.39  tff(c_16656, plain, (![A_6]: (r2_hidden('#skF_6', A_6) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(resolution, [status(thm)], [c_16607, c_14])).
% 10.27/3.39  tff(c_16699, plain, (![A_15834]: (r2_hidden('#skF_6', A_15834))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16656])).
% 10.27/3.39  tff(c_16805, plain, (![A_15836]: (A_15836='#skF_6')), inference(resolution, [status(thm)], [c_16699, c_2])).
% 10.27/3.39  tff(c_16987, plain, (![C_5, A_9496]: (r2_hidden(C_5, A_9496) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_9496)))), inference(superposition, [status(thm), theory('equality')], [c_16805, c_9355])).
% 10.27/3.39  tff(c_17058, plain, (![C_5, A_9496]: (r2_hidden(C_5, A_9496))), inference(demodulation, [status(thm), theory('equality')], [c_16661, c_16987])).
% 10.27/3.39  tff(c_17113, plain, (![C_5, A_1]: (C_5=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_17058, c_2])).
% 10.27/3.39  tff(c_18964, plain, (![A_17971]: (~r1_lattice3('#skF_5', k1_xboole_0, A_17971))), inference(superposition, [status(thm), theory('equality')], [c_16805, c_9350])).
% 10.27/3.39  tff(c_18972, plain, (![A_1, A_17971]: (~r1_lattice3('#skF_5', A_1, A_17971))), inference(superposition, [status(thm), theory('equality')], [c_17113, c_18964])).
% 10.27/3.39  tff(c_17106, plain, (![A_9500, A_10]: (m1_subset_1(A_9500, A_10))), inference(demodulation, [status(thm), theory('equality')], [c_17058, c_9360])).
% 10.27/3.39  tff(c_30, plain, (![A_21, B_28, C_29]: (m1_subset_1('#skF_3'(A_21, B_28, C_29), u1_struct_0(A_21)) | r1_lattice3(A_21, B_28, C_29) | ~m1_subset_1(C_29, u1_struct_0(A_21)) | ~l1_orders_2(A_21))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.27/3.39  tff(c_28, plain, (![A_21, B_28, C_29]: (r2_hidden('#skF_3'(A_21, B_28, C_29), B_28) | r1_lattice3(A_21, B_28, C_29) | ~m1_subset_1(C_29, u1_struct_0(A_21)) | ~l1_orders_2(A_21))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.27/3.39  tff(c_14822, plain, (![B_12095, A_12093, A_12096, C_12094, C_12092]: (r1_orders_2(A_12096, '#skF_3'(A_12093, B_12095, C_12092), C_12094) | ~m1_subset_1('#skF_3'(A_12093, B_12095, C_12092), u1_struct_0(A_12096)) | ~r2_lattice3(A_12096, B_12095, C_12094) | ~m1_subset_1(C_12094, u1_struct_0(A_12096)) | ~l1_orders_2(A_12096) | r1_lattice3(A_12093, B_12095, C_12092) | ~m1_subset_1(C_12092, u1_struct_0(A_12093)) | ~l1_orders_2(A_12093))), inference(resolution, [status(thm)], [c_28, c_12976])).
% 10.27/3.39  tff(c_14833, plain, (![A_21, B_28, C_29, C_12094]: (r1_orders_2(A_21, '#skF_3'(A_21, B_28, C_29), C_12094) | ~r2_lattice3(A_21, B_28, C_12094) | ~m1_subset_1(C_12094, u1_struct_0(A_21)) | r1_lattice3(A_21, B_28, C_29) | ~m1_subset_1(C_29, u1_struct_0(A_21)) | ~l1_orders_2(A_21))), inference(resolution, [status(thm)], [c_30, c_14822])).
% 10.27/3.39  tff(c_19224, plain, (![A_18397, B_18398, C_18399, C_18400]: (r1_orders_2(A_18397, '#skF_3'(A_18397, B_18398, C_18399), C_18400) | ~r2_lattice3(A_18397, B_18398, C_18400) | r1_lattice3(A_18397, B_18398, C_18399) | ~l1_orders_2(A_18397))), inference(demodulation, [status(thm), theory('equality')], [c_17106, c_17106, c_14833])).
% 10.27/3.39  tff(c_15263, plain, (~r1_orders_2('#skF_5', '#skF_6', '#skF_6') | r2_lattice3('#skF_5', k1_tarski('#skF_6'), '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_15249, c_34])).
% 10.27/3.39  tff(c_15278, plain, (~r1_orders_2('#skF_5', '#skF_6', '#skF_6') | r2_lattice3('#skF_5', k1_tarski('#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_15263])).
% 10.27/3.39  tff(c_15319, plain, (~r1_orders_2('#skF_5', '#skF_6', '#skF_6')), inference(splitLeft, [status(thm)], [c_15278])).
% 10.27/3.39  tff(c_16816, plain, (![A_15836]: (~r1_orders_2('#skF_5', A_15836, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_16805, c_15319])).
% 10.27/3.39  tff(c_19228, plain, (![B_18398, C_18399]: (~r2_lattice3('#skF_5', B_18398, '#skF_6') | r1_lattice3('#skF_5', B_18398, C_18399) | ~l1_orders_2('#skF_5'))), inference(resolution, [status(thm)], [c_19224, c_16816])).
% 10.27/3.39  tff(c_19327, plain, (![B_18398, C_18399]: (~r2_lattice3('#skF_5', B_18398, '#skF_6') | r1_lattice3('#skF_5', B_18398, C_18399))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_19228])).
% 10.27/3.39  tff(c_19328, plain, (![B_18398]: (~r2_lattice3('#skF_5', B_18398, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_18972, c_19327])).
% 10.27/3.39  tff(c_18541, plain, (![C_17007]: (C_17007='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_17058, c_2])).
% 10.27/3.39  tff(c_9351, plain, (r2_lattice3('#skF_5', k1_xboole_0, '#skF_6')), inference(splitRight, [status(thm)], [c_40])).
% 10.27/3.39  tff(c_18543, plain, (r2_lattice3('#skF_5', '#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_18541, c_9351])).
% 10.27/3.39  tff(c_19874, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19328, c_18543])).
% 10.27/3.39  tff(c_19876, plain, (r1_orders_2('#skF_5', '#skF_6', '#skF_6')), inference(splitRight, [status(thm)], [c_15278])).
% 10.27/3.39  tff(c_24100, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20547, c_19876])).
% 10.27/3.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.27/3.39  
% 10.27/3.39  Inference rules
% 10.27/3.39  ----------------------
% 10.27/3.39  #Ref     : 0
% 10.27/3.39  #Sup     : 4973
% 10.27/3.39  #Fact    : 8
% 10.27/3.39  #Define  : 0
% 10.27/3.39  #Split   : 5
% 10.27/3.39  #Chain   : 0
% 10.27/3.39  #Close   : 0
% 10.27/3.39  
% 10.27/3.39  Ordering : KBO
% 10.27/3.39  
% 10.27/3.39  Simplification rules
% 10.27/3.39  ----------------------
% 10.27/3.39  #Subsume      : 827
% 10.27/3.39  #Demod        : 1947
% 10.27/3.39  #Tautology    : 1012
% 10.27/3.39  #SimpNegUnit  : 195
% 10.27/3.39  #BackRed      : 88
% 10.27/3.39  
% 10.27/3.39  #Partial instantiations: 9187
% 10.27/3.39  #Strategies tried      : 1
% 10.27/3.39  
% 10.27/3.39  Timing (in seconds)
% 10.27/3.39  ----------------------
% 10.27/3.40  Preprocessing        : 0.30
% 10.27/3.40  Parsing              : 0.17
% 10.27/3.40  CNF conversion       : 0.03
% 10.27/3.40  Main loop            : 2.24
% 10.27/3.40  Inferencing          : 0.78
% 10.27/3.40  Reduction            : 0.55
% 10.27/3.40  Demodulation         : 0.36
% 10.27/3.40  BG Simplification    : 0.10
% 10.27/3.40  Subsumption          : 0.55
% 10.27/3.40  Abstraction          : 0.12
% 10.27/3.40  MUC search           : 0.00
% 10.27/3.40  Cooper               : 0.00
% 10.27/3.40  Total                : 2.59
% 10.27/3.40  Index Insertion      : 0.00
% 10.27/3.40  Index Deletion       : 0.00
% 10.27/3.40  Index Matching       : 0.00
% 10.27/3.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
