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
% DateTime   : Thu Dec  3 10:31:03 EST 2020

% Result     : Theorem 15.81s
% Output     : CNFRefutation 16.00s
% Verified   : 
% Statistics : Number of formulae       :  265 (2549 expanded)
%              Number of leaves         :   40 ( 848 expanded)
%              Depth                    :   23
%              Number of atoms          :  630 (9125 expanded)
%              Number of equality atoms :   68 ( 257 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_2 > #skF_7 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_113,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(k3_yellow_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).

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

tff(f_39,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_246,plain,(
    ! [A_83,B_84] :
      ( ~ r2_hidden('#skF_1'(A_83,B_84),B_84)
      | r1_tarski(A_83,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_259,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_246])).

tff(c_96,plain,(
    ! [C_59,A_60] :
      ( r2_hidden(C_59,k1_zfmisc_1(A_60))
      | ~ r1_tarski(C_59,A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_36,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,B_17)
      | ~ r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_121,plain,(
    ! [C_65,A_66] :
      ( m1_subset_1(C_65,k1_zfmisc_1(A_66))
      | ~ r1_tarski(C_65,A_66) ) ),
    inference(resolution,[status(thm)],[c_96,c_36])).

tff(c_58,plain,(
    ! [B_51] :
      ( ~ v1_subset_1(B_51,B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_130,plain,(
    ! [A_66] :
      ( ~ v1_subset_1(A_66,A_66)
      | ~ r1_tarski(A_66,A_66) ) ),
    inference(resolution,[status(thm)],[c_121,c_58])).

tff(c_276,plain,(
    ! [A_66] : ~ v1_subset_1(A_66,A_66) ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_130])).

tff(c_60,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_106,plain,(
    ! [B_63,A_64] :
      ( v1_xboole_0(B_63)
      | ~ m1_subset_1(B_63,A_64)
      | ~ v1_xboole_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_115,plain,
    ( v1_xboole_0('#skF_9')
    | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_8'))) ),
    inference(resolution,[status(thm)],[c_60,c_106])).

tff(c_120,plain,(
    ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_8'))) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_115])).

tff(c_224,plain,(
    ! [B_79,A_80] :
      ( r2_hidden(B_79,A_80)
      | ~ m1_subset_1(B_79,A_80)
      | v1_xboole_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16,plain,(
    ! [C_13,A_9] :
      ( r1_tarski(C_13,A_9)
      | ~ r2_hidden(C_13,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_16239,plain,(
    ! [B_769,A_770] :
      ( r1_tarski(B_769,A_770)
      | ~ m1_subset_1(B_769,k1_zfmisc_1(A_770))
      | v1_xboole_0(k1_zfmisc_1(A_770)) ) ),
    inference(resolution,[status(thm)],[c_224,c_16])).

tff(c_16257,plain,
    ( r1_tarski('#skF_9',u1_struct_0('#skF_8'))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_8'))) ),
    inference(resolution,[status(thm)],[c_60,c_16239])).

tff(c_16264,plain,(
    r1_tarski('#skF_9',u1_struct_0('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_16257])).

tff(c_236,plain,(
    ! [A_81,B_82] :
      ( r2_hidden('#skF_1'(A_81,B_82),A_81)
      | r1_tarski(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_245,plain,(
    ! [A_81,B_82] :
      ( m1_subset_1('#skF_1'(A_81,B_82),A_81)
      | r1_tarski(A_81,B_82) ) ),
    inference(resolution,[status(thm)],[c_236,c_36])).

tff(c_16185,plain,(
    ! [A_756,C_757,B_758] :
      ( m1_subset_1(A_756,C_757)
      | ~ m1_subset_1(B_758,k1_zfmisc_1(C_757))
      | ~ r2_hidden(A_756,B_758) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_16204,plain,(
    ! [A_759] :
      ( m1_subset_1(A_759,u1_struct_0('#skF_8'))
      | ~ r2_hidden(A_759,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_60,c_16185])).

tff(c_34,plain,(
    ! [B_15,A_14] :
      ( v1_xboole_0(B_15)
      | ~ m1_subset_1(B_15,A_14)
      | ~ v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16208,plain,(
    ! [A_759] :
      ( v1_xboole_0(A_759)
      | ~ v1_xboole_0(u1_struct_0('#skF_8'))
      | ~ r2_hidden(A_759,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_16204,c_34])).

tff(c_16209,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_16208])).

tff(c_16203,plain,(
    ! [A_756] :
      ( m1_subset_1(A_756,u1_struct_0('#skF_8'))
      | ~ r2_hidden(A_756,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_60,c_16185])).

tff(c_262,plain,(
    ! [C_85,B_86,A_87] :
      ( r2_hidden(C_85,B_86)
      | ~ r2_hidden(C_85,A_87)
      | ~ r1_tarski(A_87,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16509,plain,(
    ! [A_804,B_805,B_806] :
      ( r2_hidden('#skF_1'(A_804,B_805),B_806)
      | ~ r1_tarski(A_804,B_806)
      | r1_tarski(A_804,B_805) ) ),
    inference(resolution,[status(thm)],[c_6,c_262])).

tff(c_30,plain,(
    ! [B_15,A_14] :
      ( r2_hidden(B_15,A_14)
      | ~ m1_subset_1(B_15,A_14)
      | v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16333,plain,(
    ! [A_780,A_781] :
      ( r1_tarski(A_780,A_781)
      | ~ m1_subset_1('#skF_1'(A_780,A_781),A_781)
      | v1_xboole_0(A_781) ) ),
    inference(resolution,[status(thm)],[c_30,c_246])).

tff(c_16337,plain,(
    ! [A_780] :
      ( r1_tarski(A_780,u1_struct_0('#skF_8'))
      | v1_xboole_0(u1_struct_0('#skF_8'))
      | ~ r2_hidden('#skF_1'(A_780,u1_struct_0('#skF_8')),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_16203,c_16333])).

tff(c_16352,plain,(
    ! [A_780] :
      ( r1_tarski(A_780,u1_struct_0('#skF_8'))
      | ~ r2_hidden('#skF_1'(A_780,u1_struct_0('#skF_8')),'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_16209,c_16337])).

tff(c_16535,plain,(
    ! [A_807] :
      ( ~ r1_tarski(A_807,'#skF_9')
      | r1_tarski(A_807,u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_16509,c_16352])).

tff(c_272,plain,(
    ! [B_15,B_86,A_14] :
      ( r2_hidden(B_15,B_86)
      | ~ r1_tarski(A_14,B_86)
      | ~ m1_subset_1(B_15,A_14)
      | v1_xboole_0(A_14) ) ),
    inference(resolution,[status(thm)],[c_30,c_262])).

tff(c_17695,plain,(
    ! [B_884,A_885] :
      ( r2_hidden(B_884,u1_struct_0('#skF_8'))
      | ~ m1_subset_1(B_884,A_885)
      | v1_xboole_0(A_885)
      | ~ r1_tarski(A_885,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_16535,c_272])).

tff(c_17719,plain,(
    ! [A_756] :
      ( r2_hidden(A_756,u1_struct_0('#skF_8'))
      | v1_xboole_0(u1_struct_0('#skF_8'))
      | ~ r1_tarski(u1_struct_0('#skF_8'),'#skF_9')
      | ~ r2_hidden(A_756,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_16203,c_17695])).

tff(c_17754,plain,(
    ! [A_756] :
      ( r2_hidden(A_756,u1_struct_0('#skF_8'))
      | ~ r1_tarski(u1_struct_0('#skF_8'),'#skF_9')
      | ~ r2_hidden(A_756,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_16209,c_17719])).

tff(c_17767,plain,(
    ~ r1_tarski(u1_struct_0('#skF_8'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_17754])).

tff(c_62,plain,(
    v13_waybel_0('#skF_9','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_133,plain,(
    ! [B_68,A_69] :
      ( r2_hidden(B_68,A_69)
      | ~ m1_subset_1(B_68,A_69)
      | v1_xboole_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_86,plain,
    ( v1_subset_1('#skF_9',u1_struct_0('#skF_8'))
    | ~ r2_hidden(k3_yellow_0('#skF_8'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_131,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_8'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_136,plain,
    ( ~ m1_subset_1(k3_yellow_0('#skF_8'),'#skF_9')
    | v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_133,c_131])).

tff(c_146,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_8'),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_136])).

tff(c_68,plain,(
    l1_orders_2('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_80,plain,
    ( r2_hidden(k3_yellow_0('#skF_8'),'#skF_9')
    | ~ v1_subset_1('#skF_9',u1_struct_0('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_163,plain,(
    ~ v1_subset_1('#skF_9',u1_struct_0('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_80])).

tff(c_184,plain,(
    ! [B_76,A_77] :
      ( v1_subset_1(B_76,A_77)
      | B_76 = A_77
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_194,plain,
    ( v1_subset_1('#skF_9',u1_struct_0('#skF_8'))
    | u1_struct_0('#skF_8') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_60,c_184])).

tff(c_199,plain,(
    u1_struct_0('#skF_8') = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_163,c_194])).

tff(c_40,plain,(
    ! [A_21] :
      ( m1_subset_1(k3_yellow_0(A_21),u1_struct_0(A_21))
      | ~ l1_orders_2(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_206,plain,
    ( m1_subset_1(k3_yellow_0('#skF_8'),'#skF_9')
    | ~ l1_orders_2('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_40])).

tff(c_210,plain,(
    m1_subset_1(k3_yellow_0('#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_206])).

tff(c_212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_210])).

tff(c_214,plain,(
    r2_hidden(k3_yellow_0('#skF_8'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_72,plain,(
    v5_orders_2('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_70,plain,(
    v1_yellow_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_42,plain,(
    ! [A_22,B_24] :
      ( r1_orders_2(A_22,k3_yellow_0(A_22),B_24)
      | ~ m1_subset_1(B_24,u1_struct_0(A_22))
      | ~ l1_orders_2(A_22)
      | ~ v1_yellow_0(A_22)
      | ~ v5_orders_2(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_18734,plain,(
    ! [D_941,B_942,A_943,C_944] :
      ( r2_hidden(D_941,B_942)
      | ~ r1_orders_2(A_943,C_944,D_941)
      | ~ r2_hidden(C_944,B_942)
      | ~ m1_subset_1(D_941,u1_struct_0(A_943))
      | ~ m1_subset_1(C_944,u1_struct_0(A_943))
      | ~ v13_waybel_0(B_942,A_943)
      | ~ m1_subset_1(B_942,k1_zfmisc_1(u1_struct_0(A_943)))
      | ~ l1_orders_2(A_943) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_26014,plain,(
    ! [B_1195,B_1196,A_1197] :
      ( r2_hidden(B_1195,B_1196)
      | ~ r2_hidden(k3_yellow_0(A_1197),B_1196)
      | ~ m1_subset_1(k3_yellow_0(A_1197),u1_struct_0(A_1197))
      | ~ v13_waybel_0(B_1196,A_1197)
      | ~ m1_subset_1(B_1196,k1_zfmisc_1(u1_struct_0(A_1197)))
      | ~ m1_subset_1(B_1195,u1_struct_0(A_1197))
      | ~ l1_orders_2(A_1197)
      | ~ v1_yellow_0(A_1197)
      | ~ v5_orders_2(A_1197)
      | v2_struct_0(A_1197) ) ),
    inference(resolution,[status(thm)],[c_42,c_18734])).

tff(c_26025,plain,(
    ! [B_1195,B_1196] :
      ( r2_hidden(B_1195,B_1196)
      | ~ r2_hidden(k3_yellow_0('#skF_8'),B_1196)
      | ~ v13_waybel_0(B_1196,'#skF_8')
      | ~ m1_subset_1(B_1196,k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ m1_subset_1(B_1195,u1_struct_0('#skF_8'))
      | ~ l1_orders_2('#skF_8')
      | ~ v1_yellow_0('#skF_8')
      | ~ v5_orders_2('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ r2_hidden(k3_yellow_0('#skF_8'),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_16203,c_26014])).

tff(c_26048,plain,(
    ! [B_1195,B_1196] :
      ( r2_hidden(B_1195,B_1196)
      | ~ r2_hidden(k3_yellow_0('#skF_8'),B_1196)
      | ~ v13_waybel_0(B_1196,'#skF_8')
      | ~ m1_subset_1(B_1196,k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ m1_subset_1(B_1195,u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_72,c_70,c_68,c_26025])).

tff(c_26217,plain,(
    ! [B_1201,B_1202] :
      ( r2_hidden(B_1201,B_1202)
      | ~ r2_hidden(k3_yellow_0('#skF_8'),B_1202)
      | ~ v13_waybel_0(B_1202,'#skF_8')
      | ~ m1_subset_1(B_1202,k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ m1_subset_1(B_1201,u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_26048])).

tff(c_26331,plain,(
    ! [B_1201] :
      ( r2_hidden(B_1201,'#skF_9')
      | ~ r2_hidden(k3_yellow_0('#skF_8'),'#skF_9')
      | ~ v13_waybel_0('#skF_9','#skF_8')
      | ~ m1_subset_1(B_1201,u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_60,c_26217])).

tff(c_26386,plain,(
    ! [B_1203] :
      ( r2_hidden(B_1203,'#skF_9')
      | ~ m1_subset_1(B_1203,u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_214,c_26331])).

tff(c_26979,plain,(
    ! [B_1213] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_8'),B_1213),'#skF_9')
      | r1_tarski(u1_struct_0('#skF_8'),B_1213) ) ),
    inference(resolution,[status(thm)],[c_245,c_26386])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_27001,plain,(
    r1_tarski(u1_struct_0('#skF_8'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_26979,c_4])).

tff(c_27019,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17767,c_17767,c_27001])).

tff(c_27021,plain,(
    r1_tarski(u1_struct_0('#skF_8'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_17754])).

tff(c_100,plain,(
    ! [C_59,A_60] :
      ( m1_subset_1(C_59,k1_zfmisc_1(A_60))
      | ~ r1_tarski(C_59,A_60) ) ),
    inference(resolution,[status(thm)],[c_96,c_36])).

tff(c_16218,plain,(
    ! [A_763,A_764,C_765] :
      ( m1_subset_1(A_763,A_764)
      | ~ r2_hidden(A_763,C_765)
      | ~ r1_tarski(C_765,A_764) ) ),
    inference(resolution,[status(thm)],[c_100,c_16185])).

tff(c_16231,plain,(
    ! [B_15,A_764,A_14] :
      ( m1_subset_1(B_15,A_764)
      | ~ r1_tarski(A_14,A_764)
      | ~ m1_subset_1(B_15,A_14)
      | v1_xboole_0(A_14) ) ),
    inference(resolution,[status(thm)],[c_30,c_16218])).

tff(c_27037,plain,(
    ! [B_15] :
      ( m1_subset_1(B_15,'#skF_9')
      | ~ m1_subset_1(B_15,u1_struct_0('#skF_8'))
      | v1_xboole_0(u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_27021,c_16231])).

tff(c_27255,plain,(
    ! [B_1217] :
      ( m1_subset_1(B_1217,'#skF_9')
      | ~ m1_subset_1(B_1217,u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_16209,c_27037])).

tff(c_27325,plain,(
    ! [B_82] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_8'),B_82),'#skF_9')
      | r1_tarski(u1_struct_0('#skF_8'),B_82) ) ),
    inference(resolution,[status(thm)],[c_245,c_27255])).

tff(c_16409,plain,(
    ! [B_793,B_794,A_795] :
      ( r2_hidden(B_793,B_794)
      | ~ r1_tarski(A_795,B_794)
      | ~ m1_subset_1(B_793,A_795)
      | v1_xboole_0(A_795) ) ),
    inference(resolution,[status(thm)],[c_30,c_262])).

tff(c_16413,plain,(
    ! [B_793] :
      ( r2_hidden(B_793,u1_struct_0('#skF_8'))
      | ~ m1_subset_1(B_793,'#skF_9')
      | v1_xboole_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_16264,c_16409])).

tff(c_16425,plain,(
    ! [B_796] :
      ( r2_hidden(B_796,u1_struct_0('#skF_8'))
      | ~ m1_subset_1(B_796,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_16413])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16447,plain,(
    ! [B_796,B_2] :
      ( r2_hidden(B_796,B_2)
      | ~ r1_tarski(u1_struct_0('#skF_8'),B_2)
      | ~ m1_subset_1(B_796,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_16425,c_2])).

tff(c_27078,plain,(
    ! [B_1214] :
      ( r2_hidden(B_1214,'#skF_9')
      | ~ m1_subset_1(B_1214,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_27021,c_16447])).

tff(c_27415,plain,(
    ! [B_1226,B_1227] :
      ( r2_hidden(B_1226,B_1227)
      | ~ r1_tarski('#skF_9',B_1227)
      | ~ m1_subset_1(B_1226,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_27078,c_2])).

tff(c_27644,plain,(
    ! [A_1240,B_1241] :
      ( r1_tarski(A_1240,B_1241)
      | ~ r1_tarski('#skF_9',B_1241)
      | ~ m1_subset_1('#skF_1'(A_1240,B_1241),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_27415,c_4])).

tff(c_27659,plain,(
    ! [B_82] :
      ( ~ r1_tarski('#skF_9',B_82)
      | r1_tarski(u1_struct_0('#skF_8'),B_82) ) ),
    inference(resolution,[status(thm)],[c_27325,c_27644])).

tff(c_244,plain,(
    ! [A_9,B_82] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(A_9),B_82),A_9)
      | r1_tarski(k1_zfmisc_1(A_9),B_82) ) ),
    inference(resolution,[status(thm)],[c_236,c_16])).

tff(c_16534,plain,(
    ! [A_804,B_805,B_806] :
      ( m1_subset_1('#skF_1'(A_804,B_805),B_806)
      | ~ r1_tarski(A_804,B_806)
      | r1_tarski(A_804,B_805) ) ),
    inference(resolution,[status(thm)],[c_16509,c_36])).

tff(c_27043,plain,(
    ! [B_15] :
      ( r2_hidden(B_15,'#skF_9')
      | ~ m1_subset_1(B_15,u1_struct_0('#skF_8'))
      | v1_xboole_0(u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_27021,c_272])).

tff(c_27177,plain,(
    ! [B_1216] :
      ( r2_hidden(B_1216,'#skF_9')
      | ~ m1_subset_1(B_1216,u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_16209,c_27043])).

tff(c_28560,plain,(
    ! [A_1281,B_1282] :
      ( r2_hidden('#skF_1'(A_1281,B_1282),'#skF_9')
      | ~ r1_tarski(A_1281,u1_struct_0('#skF_8'))
      | r1_tarski(A_1281,B_1282) ) ),
    inference(resolution,[status(thm)],[c_16534,c_27177])).

tff(c_28592,plain,(
    ! [A_1283] :
      ( ~ r1_tarski(A_1283,u1_struct_0('#skF_8'))
      | r1_tarski(A_1283,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_28560,c_4])).

tff(c_29430,plain,(
    ! [B_1320] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(u1_struct_0('#skF_8')),B_1320),'#skF_9')
      | r1_tarski(k1_zfmisc_1(u1_struct_0('#skF_8')),B_1320) ) ),
    inference(resolution,[status(thm)],[c_244,c_28592])).

tff(c_18,plain,(
    ! [C_13,A_9] :
      ( r2_hidden(C_13,k1_zfmisc_1(A_9))
      | ~ r1_tarski(C_13,A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_261,plain,(
    ! [A_83,A_9] :
      ( r1_tarski(A_83,k1_zfmisc_1(A_9))
      | ~ r1_tarski('#skF_1'(A_83,k1_zfmisc_1(A_9)),A_9) ) ),
    inference(resolution,[status(thm)],[c_18,c_246])).

tff(c_29480,plain,(
    r1_tarski(k1_zfmisc_1(u1_struct_0('#skF_8')),k1_zfmisc_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_29430,c_261])).

tff(c_16233,plain,(
    ! [C_13,A_764,A_9] :
      ( m1_subset_1(C_13,A_764)
      | ~ r1_tarski(k1_zfmisc_1(A_9),A_764)
      | ~ r1_tarski(C_13,A_9) ) ),
    inference(resolution,[status(thm)],[c_18,c_16218])).

tff(c_29679,plain,(
    ! [C_1324] :
      ( m1_subset_1(C_1324,k1_zfmisc_1('#skF_9'))
      | ~ r1_tarski(C_1324,u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_29480,c_16233])).

tff(c_29690,plain,
    ( m1_subset_1(u1_struct_0('#skF_8'),k1_zfmisc_1('#skF_9'))
    | ~ r1_tarski('#skF_9',u1_struct_0('#skF_8')) ),
    inference(resolution,[status(thm)],[c_27659,c_29679])).

tff(c_29721,plain,(
    m1_subset_1(u1_struct_0('#skF_8'),k1_zfmisc_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16264,c_29690])).

tff(c_56,plain,(
    ! [B_51,A_50] :
      ( v1_subset_1(B_51,A_50)
      | B_51 = A_50
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_29791,plain,
    ( v1_subset_1(u1_struct_0('#skF_8'),'#skF_9')
    | u1_struct_0('#skF_8') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_29721,c_56])).

tff(c_29963,plain,(
    u1_struct_0('#skF_8') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_29791])).

tff(c_213,plain,(
    v1_subset_1('#skF_9',u1_struct_0('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_30052,plain,(
    v1_subset_1('#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29963,c_213])).

tff(c_30064,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_276,c_30052])).

tff(c_30066,plain,(
    u1_struct_0('#skF_8') != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_29791])).

tff(c_16471,plain,(
    ! [A_802,B_803] :
      ( r2_hidden('#skF_2'(A_802,B_803),B_803)
      | r2_hidden('#skF_3'(A_802,B_803),A_802)
      | B_803 = A_802 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_30982,plain,(
    ! [A_1359,B_1360,B_1361] :
      ( r2_hidden('#skF_3'(A_1359,B_1360),B_1361)
      | ~ r1_tarski(A_1359,B_1361)
      | r2_hidden('#skF_2'(A_1359,B_1360),B_1360)
      | B_1360 = A_1359 ) ),
    inference(resolution,[status(thm)],[c_16471,c_2])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_7)
      | ~ r2_hidden('#skF_3'(A_6,B_7),B_7)
      | B_7 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_31082,plain,(
    ! [A_1362,B_1363] :
      ( ~ r1_tarski(A_1362,B_1363)
      | r2_hidden('#skF_2'(A_1362,B_1363),B_1363)
      | B_1363 = A_1362 ) ),
    inference(resolution,[status(thm)],[c_30982,c_10])).

tff(c_16201,plain,(
    ! [A_756,A_60,C_59] :
      ( m1_subset_1(A_756,A_60)
      | ~ r2_hidden(A_756,C_59)
      | ~ r1_tarski(C_59,A_60) ) ),
    inference(resolution,[status(thm)],[c_100,c_16185])).

tff(c_31988,plain,(
    ! [A_1397,B_1398,A_1399] :
      ( m1_subset_1('#skF_2'(A_1397,B_1398),A_1399)
      | ~ r1_tarski(B_1398,A_1399)
      | ~ r1_tarski(A_1397,B_1398)
      | B_1398 = A_1397 ) ),
    inference(resolution,[status(thm)],[c_31082,c_16201])).

tff(c_16724,plain,(
    ! [A_822,B_823] :
      ( ~ r2_hidden('#skF_2'(A_822,B_823),A_822)
      | r2_hidden('#skF_3'(A_822,B_823),A_822)
      | B_823 = A_822 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16758,plain,(
    ! [A_822,B_823] :
      ( m1_subset_1('#skF_3'(A_822,B_823),A_822)
      | ~ r2_hidden('#skF_2'(A_822,B_823),A_822)
      | B_823 = A_822 ) ),
    inference(resolution,[status(thm)],[c_16724,c_36])).

tff(c_28272,plain,(
    ! [B_1265] :
      ( m1_subset_1('#skF_3'('#skF_9',B_1265),'#skF_9')
      | B_1265 = '#skF_9'
      | ~ m1_subset_1('#skF_2'('#skF_9',B_1265),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_27078,c_16758])).

tff(c_16564,plain,(
    ! [B_15,A_807] :
      ( r2_hidden(B_15,u1_struct_0('#skF_8'))
      | ~ m1_subset_1(B_15,A_807)
      | v1_xboole_0(A_807)
      | ~ r1_tarski(A_807,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_16535,c_272])).

tff(c_28274,plain,(
    ! [B_1265] :
      ( r2_hidden('#skF_3'('#skF_9',B_1265),u1_struct_0('#skF_8'))
      | v1_xboole_0('#skF_9')
      | ~ r1_tarski('#skF_9','#skF_9')
      | B_1265 = '#skF_9'
      | ~ m1_subset_1('#skF_2'('#skF_9',B_1265),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_28272,c_16564])).

tff(c_28282,plain,(
    ! [B_1265] :
      ( r2_hidden('#skF_3'('#skF_9',B_1265),u1_struct_0('#skF_8'))
      | v1_xboole_0('#skF_9')
      | B_1265 = '#skF_9'
      | ~ m1_subset_1('#skF_2'('#skF_9',B_1265),'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_28274])).

tff(c_28283,plain,(
    ! [B_1265] :
      ( r2_hidden('#skF_3'('#skF_9',B_1265),u1_struct_0('#skF_8'))
      | B_1265 = '#skF_9'
      | ~ m1_subset_1('#skF_2'('#skF_9',B_1265),'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_28282])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7),A_6)
      | ~ r2_hidden('#skF_3'(A_6,B_7),B_7)
      | B_7 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28316,plain,(
    ! [B_1267] :
      ( ~ r2_hidden('#skF_3'('#skF_9',B_1267),B_1267)
      | B_1267 = '#skF_9'
      | ~ m1_subset_1('#skF_2'('#skF_9',B_1267),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_27078,c_8])).

tff(c_28369,plain,
    ( u1_struct_0('#skF_8') = '#skF_9'
    | ~ m1_subset_1('#skF_2'('#skF_9',u1_struct_0('#skF_8')),'#skF_9') ),
    inference(resolution,[status(thm)],[c_28283,c_28316])).

tff(c_28385,plain,(
    ~ m1_subset_1('#skF_2'('#skF_9',u1_struct_0('#skF_8')),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_28369])).

tff(c_32003,plain,
    ( ~ r1_tarski(u1_struct_0('#skF_8'),'#skF_9')
    | ~ r1_tarski('#skF_9',u1_struct_0('#skF_8'))
    | u1_struct_0('#skF_8') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_31988,c_28385])).

tff(c_32044,plain,(
    u1_struct_0('#skF_8') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16264,c_27021,c_32003])).

tff(c_32046,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30066,c_32044])).

tff(c_32047,plain,(
    u1_struct_0('#skF_8') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_28369])).

tff(c_32113,plain,(
    v1_subset_1('#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32047,c_213])).

tff(c_32123,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_276,c_32113])).

tff(c_32125,plain,(
    v1_xboole_0(u1_struct_0('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_16208])).

tff(c_32126,plain,(
    ! [A_1400,B_1401] :
      ( r2_hidden('#skF_2'(A_1400,B_1401),B_1401)
      | r2_hidden('#skF_3'(A_1400,B_1401),A_1400)
      | B_1401 = A_1400 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_33234,plain,(
    ! [A_1505,B_1506] :
      ( m1_subset_1('#skF_3'(A_1505,B_1506),A_1505)
      | r2_hidden('#skF_2'(A_1505,B_1506),B_1506)
      | B_1506 = A_1505 ) ),
    inference(resolution,[status(thm)],[c_32126,c_36])).

tff(c_35276,plain,(
    ! [A_1609,B_1610] :
      ( v1_xboole_0('#skF_3'(A_1609,B_1610))
      | ~ v1_xboole_0(A_1609)
      | r2_hidden('#skF_2'(A_1609,B_1610),B_1610)
      | B_1610 = A_1609 ) ),
    inference(resolution,[status(thm)],[c_33234,c_34])).

tff(c_35334,plain,(
    ! [A_1609,B_1610] :
      ( m1_subset_1('#skF_2'(A_1609,B_1610),B_1610)
      | v1_xboole_0('#skF_3'(A_1609,B_1610))
      | ~ v1_xboole_0(A_1609)
      | B_1610 = A_1609 ) ),
    inference(resolution,[status(thm)],[c_35276,c_36])).

tff(c_32236,plain,(
    ! [B_1410,A_1411] :
      ( r1_tarski(B_1410,A_1411)
      | ~ m1_subset_1(B_1410,k1_zfmisc_1(A_1411))
      | v1_xboole_0(k1_zfmisc_1(A_1411)) ) ),
    inference(resolution,[status(thm)],[c_224,c_16])).

tff(c_32254,plain,
    ( r1_tarski('#skF_9',u1_struct_0('#skF_8'))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_8'))) ),
    inference(resolution,[status(thm)],[c_60,c_32236])).

tff(c_32261,plain,(
    r1_tarski('#skF_9',u1_struct_0('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_32254])).

tff(c_32540,plain,(
    ! [B_1446,B_1447,A_1448] :
      ( r2_hidden(B_1446,B_1447)
      | ~ r1_tarski(A_1448,B_1447)
      | ~ m1_subset_1(B_1446,A_1448)
      | v1_xboole_0(A_1448) ) ),
    inference(resolution,[status(thm)],[c_30,c_262])).

tff(c_32544,plain,(
    ! [B_1446] :
      ( r2_hidden(B_1446,u1_struct_0('#skF_8'))
      | ~ m1_subset_1(B_1446,'#skF_9')
      | v1_xboole_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_32261,c_32540])).

tff(c_32552,plain,(
    ! [B_1446] :
      ( r2_hidden(B_1446,u1_struct_0('#skF_8'))
      | ~ m1_subset_1(B_1446,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_32544])).

tff(c_32371,plain,(
    ! [A_1426,B_1427] :
      ( ~ r2_hidden('#skF_2'(A_1426,B_1427),A_1426)
      | r2_hidden('#skF_3'(A_1426,B_1427),A_1426)
      | B_1427 = A_1426 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_35512,plain,(
    ! [A_1618,B_1619,B_1620] :
      ( r2_hidden('#skF_3'(A_1618,B_1619),B_1620)
      | ~ r1_tarski(A_1618,B_1620)
      | ~ r2_hidden('#skF_2'(A_1618,B_1619),A_1618)
      | B_1619 = A_1618 ) ),
    inference(resolution,[status(thm)],[c_32371,c_2])).

tff(c_35599,plain,(
    ! [B_1623,B_1624] :
      ( r2_hidden('#skF_3'(u1_struct_0('#skF_8'),B_1623),B_1624)
      | ~ r1_tarski(u1_struct_0('#skF_8'),B_1624)
      | u1_struct_0('#skF_8') = B_1623
      | ~ m1_subset_1('#skF_2'(u1_struct_0('#skF_8'),B_1623),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_32552,c_35512])).

tff(c_32566,plain,(
    ! [B_1451] :
      ( r2_hidden(B_1451,u1_struct_0('#skF_8'))
      | ~ m1_subset_1(B_1451,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_32544])).

tff(c_32587,plain,(
    ! [B_7] :
      ( ~ r2_hidden('#skF_3'(u1_struct_0('#skF_8'),B_7),B_7)
      | u1_struct_0('#skF_8') = B_7
      | ~ m1_subset_1('#skF_2'(u1_struct_0('#skF_8'),B_7),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_32566,c_8])).

tff(c_35664,plain,(
    ! [B_1626] :
      ( ~ r1_tarski(u1_struct_0('#skF_8'),B_1626)
      | u1_struct_0('#skF_8') = B_1626
      | ~ m1_subset_1('#skF_2'(u1_struct_0('#skF_8'),B_1626),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_35599,c_32587])).

tff(c_35668,plain,
    ( ~ r1_tarski(u1_struct_0('#skF_8'),'#skF_9')
    | v1_xboole_0('#skF_3'(u1_struct_0('#skF_8'),'#skF_9'))
    | ~ v1_xboole_0(u1_struct_0('#skF_8'))
    | u1_struct_0('#skF_8') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_35334,c_35664])).

tff(c_35678,plain,
    ( ~ r1_tarski(u1_struct_0('#skF_8'),'#skF_9')
    | v1_xboole_0('#skF_3'(u1_struct_0('#skF_8'),'#skF_9'))
    | u1_struct_0('#skF_8') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32125,c_35668])).

tff(c_35680,plain,(
    ~ r1_tarski(u1_struct_0('#skF_8'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_35678])).

tff(c_33135,plain,(
    ! [A_1501,B_1502] :
      ( m1_subset_1('#skF_3'(A_1501,B_1502),A_1501)
      | ~ r2_hidden('#skF_2'(A_1501,B_1502),A_1501)
      | B_1502 = A_1501 ) ),
    inference(resolution,[status(thm)],[c_32371,c_36])).

tff(c_33409,plain,(
    ! [B_1515] :
      ( m1_subset_1('#skF_3'(u1_struct_0('#skF_8'),B_1515),u1_struct_0('#skF_8'))
      | u1_struct_0('#skF_8') = B_1515
      | ~ m1_subset_1('#skF_2'(u1_struct_0('#skF_8'),B_1515),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_32552,c_33135])).

tff(c_33412,plain,(
    ! [B_1515] :
      ( v1_xboole_0('#skF_3'(u1_struct_0('#skF_8'),B_1515))
      | ~ v1_xboole_0(u1_struct_0('#skF_8'))
      | u1_struct_0('#skF_8') = B_1515
      | ~ m1_subset_1('#skF_2'(u1_struct_0('#skF_8'),B_1515),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_33409,c_34])).

tff(c_38698,plain,(
    ! [B_1753] :
      ( v1_xboole_0('#skF_3'(u1_struct_0('#skF_8'),B_1753))
      | u1_struct_0('#skF_8') = B_1753
      | ~ m1_subset_1('#skF_2'(u1_struct_0('#skF_8'),B_1753),'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32125,c_33412])).

tff(c_38714,plain,
    ( v1_xboole_0('#skF_3'(u1_struct_0('#skF_8'),'#skF_9'))
    | ~ v1_xboole_0(u1_struct_0('#skF_8'))
    | u1_struct_0('#skF_8') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_35334,c_38698])).

tff(c_38727,plain,
    ( v1_xboole_0('#skF_3'(u1_struct_0('#skF_8'),'#skF_9'))
    | u1_struct_0('#skF_8') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32125,c_38714])).

tff(c_38729,plain,(
    u1_struct_0('#skF_8') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_38727])).

tff(c_32506,plain,(
    ! [A_1441,B_1442,B_1443] :
      ( r2_hidden('#skF_1'(A_1441,B_1442),B_1443)
      | ~ r1_tarski(A_1441,B_1443)
      | r1_tarski(A_1441,B_1442) ) ),
    inference(resolution,[status(thm)],[c_6,c_262])).

tff(c_32537,plain,(
    ! [A_1441,B_1442,A_9] :
      ( r1_tarski('#skF_1'(A_1441,B_1442),A_9)
      | ~ r1_tarski(A_1441,k1_zfmisc_1(A_9))
      | r1_tarski(A_1441,B_1442) ) ),
    inference(resolution,[status(thm)],[c_32506,c_16])).

tff(c_32631,plain,(
    ! [A_1460,B_1461,B_1462] :
      ( m1_subset_1('#skF_1'(A_1460,B_1461),B_1462)
      | ~ r1_tarski(A_1460,B_1462)
      | r1_tarski(A_1460,B_1461) ) ),
    inference(resolution,[status(thm)],[c_32506,c_36])).

tff(c_32594,plain,(
    ! [A_1] :
      ( r1_tarski(A_1,u1_struct_0('#skF_8'))
      | ~ m1_subset_1('#skF_1'(A_1,u1_struct_0('#skF_8')),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_32566,c_4])).

tff(c_32665,plain,(
    ! [A_1463] :
      ( ~ r1_tarski(A_1463,'#skF_9')
      | r1_tarski(A_1463,u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_32631,c_32594])).

tff(c_33631,plain,(
    ! [A_1534] :
      ( r1_tarski(A_1534,k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ r1_tarski('#skF_1'(A_1534,k1_zfmisc_1(u1_struct_0('#skF_8'))),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_32665,c_261])).

tff(c_33775,plain,(
    ! [A_1538] :
      ( ~ r1_tarski(A_1538,k1_zfmisc_1('#skF_9'))
      | r1_tarski(A_1538,k1_zfmisc_1(u1_struct_0('#skF_8'))) ) ),
    inference(resolution,[status(thm)],[c_32537,c_33631])).

tff(c_274,plain,(
    ! [C_13,B_86,A_9] :
      ( r2_hidden(C_13,B_86)
      | ~ r1_tarski(k1_zfmisc_1(A_9),B_86)
      | ~ r1_tarski(C_13,A_9) ) ),
    inference(resolution,[status(thm)],[c_18,c_262])).

tff(c_35818,plain,(
    ! [C_1631,A_1632] :
      ( r2_hidden(C_1631,k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ r1_tarski(C_1631,A_1632)
      | ~ r1_tarski(k1_zfmisc_1(A_1632),k1_zfmisc_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_33775,c_274])).

tff(c_35855,plain,
    ( r2_hidden('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_8')))
    | ~ r1_tarski(k1_zfmisc_1(u1_struct_0('#skF_8')),k1_zfmisc_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_32261,c_35818])).

tff(c_35935,plain,(
    ~ r1_tarski(k1_zfmisc_1(u1_struct_0('#skF_8')),k1_zfmisc_1('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_35855])).

tff(c_38746,plain,(
    ~ r1_tarski(k1_zfmisc_1('#skF_9'),k1_zfmisc_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38729,c_35935])).

tff(c_38823,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_38746])).

tff(c_38825,plain,(
    u1_struct_0('#skF_8') != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_38727])).

tff(c_33169,plain,(
    ! [A_1503,B_1504] :
      ( m1_subset_1('#skF_2'(A_1503,B_1504),B_1504)
      | r2_hidden('#skF_3'(A_1503,B_1504),A_1503)
      | B_1504 = A_1503 ) ),
    inference(resolution,[status(thm)],[c_32126,c_36])).

tff(c_33333,plain,(
    ! [A_1510,B_1511] :
      ( m1_subset_1('#skF_3'(A_1510,B_1511),A_1510)
      | m1_subset_1('#skF_2'(A_1510,B_1511),B_1511)
      | B_1511 = A_1510 ) ),
    inference(resolution,[status(thm)],[c_33169,c_36])).

tff(c_33378,plain,(
    ! [A_1510,B_1511] :
      ( v1_xboole_0('#skF_2'(A_1510,B_1511))
      | ~ v1_xboole_0(B_1511)
      | m1_subset_1('#skF_3'(A_1510,B_1511),A_1510)
      | B_1511 = A_1510 ) ),
    inference(resolution,[status(thm)],[c_33333,c_34])).

tff(c_33105,plain,(
    ! [A_1498] :
      ( r2_hidden('#skF_2'(A_1498,u1_struct_0('#skF_8')),u1_struct_0('#skF_8'))
      | u1_struct_0('#skF_8') = A_1498
      | ~ m1_subset_1('#skF_3'(A_1498,u1_struct_0('#skF_8')),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_32566,c_10])).

tff(c_39968,plain,(
    ! [A_1785] :
      ( m1_subset_1('#skF_2'(A_1785,u1_struct_0('#skF_8')),u1_struct_0('#skF_8'))
      | u1_struct_0('#skF_8') = A_1785
      | ~ m1_subset_1('#skF_3'(A_1785,u1_struct_0('#skF_8')),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_33105,c_36])).

tff(c_39984,plain,(
    ! [A_1785] :
      ( v1_xboole_0('#skF_2'(A_1785,u1_struct_0('#skF_8')))
      | ~ v1_xboole_0(u1_struct_0('#skF_8'))
      | u1_struct_0('#skF_8') = A_1785
      | ~ m1_subset_1('#skF_3'(A_1785,u1_struct_0('#skF_8')),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_39968,c_34])).

tff(c_40001,plain,(
    ! [A_1786] :
      ( v1_xboole_0('#skF_2'(A_1786,u1_struct_0('#skF_8')))
      | u1_struct_0('#skF_8') = A_1786
      | ~ m1_subset_1('#skF_3'(A_1786,u1_struct_0('#skF_8')),'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32125,c_39984])).

tff(c_40013,plain,
    ( v1_xboole_0('#skF_2'('#skF_9',u1_struct_0('#skF_8')))
    | ~ v1_xboole_0(u1_struct_0('#skF_8'))
    | u1_struct_0('#skF_8') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_33378,c_40001])).

tff(c_40029,plain,
    ( v1_xboole_0('#skF_2'('#skF_9',u1_struct_0('#skF_8')))
    | u1_struct_0('#skF_8') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32125,c_40013])).

tff(c_40030,plain,(
    v1_xboole_0('#skF_2'('#skF_9',u1_struct_0('#skF_8'))) ),
    inference(negUnitSimplification,[status(thm)],[c_38825,c_40029])).

tff(c_32,plain,(
    ! [B_15,A_14] :
      ( m1_subset_1(B_15,A_14)
      | ~ v1_xboole_0(B_15)
      | ~ v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_34642,plain,(
    ! [D_1577,B_1578,A_1579,C_1580] :
      ( r2_hidden(D_1577,B_1578)
      | ~ r1_orders_2(A_1579,C_1580,D_1577)
      | ~ r2_hidden(C_1580,B_1578)
      | ~ m1_subset_1(D_1577,u1_struct_0(A_1579))
      | ~ m1_subset_1(C_1580,u1_struct_0(A_1579))
      | ~ v13_waybel_0(B_1578,A_1579)
      | ~ m1_subset_1(B_1578,k1_zfmisc_1(u1_struct_0(A_1579)))
      | ~ l1_orders_2(A_1579) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_42414,plain,(
    ! [B_1848,B_1849,A_1850] :
      ( r2_hidden(B_1848,B_1849)
      | ~ r2_hidden(k3_yellow_0(A_1850),B_1849)
      | ~ m1_subset_1(k3_yellow_0(A_1850),u1_struct_0(A_1850))
      | ~ v13_waybel_0(B_1849,A_1850)
      | ~ m1_subset_1(B_1849,k1_zfmisc_1(u1_struct_0(A_1850)))
      | ~ m1_subset_1(B_1848,u1_struct_0(A_1850))
      | ~ l1_orders_2(A_1850)
      | ~ v1_yellow_0(A_1850)
      | ~ v5_orders_2(A_1850)
      | v2_struct_0(A_1850) ) ),
    inference(resolution,[status(thm)],[c_42,c_34642])).

tff(c_42428,plain,(
    ! [B_1848,B_1849] :
      ( r2_hidden(B_1848,B_1849)
      | ~ r2_hidden(k3_yellow_0('#skF_8'),B_1849)
      | ~ v13_waybel_0(B_1849,'#skF_8')
      | ~ m1_subset_1(B_1849,k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ m1_subset_1(B_1848,u1_struct_0('#skF_8'))
      | ~ l1_orders_2('#skF_8')
      | ~ v1_yellow_0('#skF_8')
      | ~ v5_orders_2('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ r2_hidden(k3_yellow_0('#skF_8'),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_16203,c_42414])).

tff(c_42455,plain,(
    ! [B_1848,B_1849] :
      ( r2_hidden(B_1848,B_1849)
      | ~ r2_hidden(k3_yellow_0('#skF_8'),B_1849)
      | ~ v13_waybel_0(B_1849,'#skF_8')
      | ~ m1_subset_1(B_1849,k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ m1_subset_1(B_1848,u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_72,c_70,c_68,c_42428])).

tff(c_42861,plain,(
    ! [B_1860,B_1861] :
      ( r2_hidden(B_1860,B_1861)
      | ~ r2_hidden(k3_yellow_0('#skF_8'),B_1861)
      | ~ v13_waybel_0(B_1861,'#skF_8')
      | ~ m1_subset_1(B_1861,k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ m1_subset_1(B_1860,u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_42455])).

tff(c_42993,plain,(
    ! [B_1860] :
      ( r2_hidden(B_1860,'#skF_9')
      | ~ r2_hidden(k3_yellow_0('#skF_8'),'#skF_9')
      | ~ v13_waybel_0('#skF_9','#skF_8')
      | ~ m1_subset_1(B_1860,u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_60,c_42861])).

tff(c_43046,plain,(
    ! [B_1862] :
      ( r2_hidden(B_1862,'#skF_9')
      | ~ m1_subset_1(B_1862,u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_214,c_42993])).

tff(c_43254,plain,(
    ! [B_15] :
      ( r2_hidden(B_15,'#skF_9')
      | ~ v1_xboole_0(B_15)
      | ~ v1_xboole_0(u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_32,c_43046])).

tff(c_43330,plain,(
    ! [B_1863] :
      ( r2_hidden(B_1863,'#skF_9')
      | ~ v1_xboole_0(B_1863) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32125,c_43254])).

tff(c_43428,plain,(
    ! [B_1863] :
      ( m1_subset_1(B_1863,'#skF_9')
      | ~ v1_xboole_0(B_1863) ) ),
    inference(resolution,[status(thm)],[c_43330,c_36])).

tff(c_33167,plain,(
    ! [A_14,B_1502] :
      ( m1_subset_1('#skF_3'(A_14,B_1502),A_14)
      | B_1502 = A_14
      | ~ m1_subset_1('#skF_2'(A_14,B_1502),A_14)
      | v1_xboole_0(A_14) ) ),
    inference(resolution,[status(thm)],[c_30,c_33135])).

tff(c_43429,plain,(
    ! [B_1864] :
      ( m1_subset_1(B_1864,'#skF_9')
      | ~ v1_xboole_0(B_1864) ) ),
    inference(resolution,[status(thm)],[c_43330,c_36])).

tff(c_32556,plain,(
    ! [A_1449,B_1450] :
      ( ~ r2_hidden('#skF_2'(A_1449,B_1450),A_1449)
      | ~ r2_hidden('#skF_3'(A_1449,B_1450),B_1450)
      | B_1450 = A_1449 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_35335,plain,(
    ! [A_1611,B_1612] :
      ( ~ r2_hidden('#skF_3'(A_1611,B_1612),B_1612)
      | B_1612 = A_1611
      | ~ m1_subset_1('#skF_2'(A_1611,B_1612),A_1611)
      | v1_xboole_0(A_1611) ) ),
    inference(resolution,[status(thm)],[c_30,c_32556])).

tff(c_35372,plain,(
    ! [A_1611] :
      ( u1_struct_0('#skF_8') = A_1611
      | ~ m1_subset_1('#skF_2'(A_1611,u1_struct_0('#skF_8')),A_1611)
      | v1_xboole_0(A_1611)
      | ~ m1_subset_1('#skF_3'(A_1611,u1_struct_0('#skF_8')),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_32552,c_35335])).

tff(c_43464,plain,
    ( u1_struct_0('#skF_8') = '#skF_9'
    | v1_xboole_0('#skF_9')
    | ~ m1_subset_1('#skF_3'('#skF_9',u1_struct_0('#skF_8')),'#skF_9')
    | ~ v1_xboole_0('#skF_2'('#skF_9',u1_struct_0('#skF_8'))) ),
    inference(resolution,[status(thm)],[c_43429,c_35372])).

tff(c_43517,plain,
    ( u1_struct_0('#skF_8') = '#skF_9'
    | v1_xboole_0('#skF_9')
    | ~ m1_subset_1('#skF_3'('#skF_9',u1_struct_0('#skF_8')),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40030,c_43464])).

tff(c_43518,plain,(
    ~ m1_subset_1('#skF_3'('#skF_9',u1_struct_0('#skF_8')),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_38825,c_43517])).

tff(c_43937,plain,
    ( u1_struct_0('#skF_8') = '#skF_9'
    | ~ m1_subset_1('#skF_2'('#skF_9',u1_struct_0('#skF_8')),'#skF_9')
    | v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_33167,c_43518])).

tff(c_43957,plain,(
    ~ m1_subset_1('#skF_2'('#skF_9',u1_struct_0('#skF_8')),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_38825,c_43937])).

tff(c_43989,plain,(
    ~ v1_xboole_0('#skF_2'('#skF_9',u1_struct_0('#skF_8'))) ),
    inference(resolution,[status(thm)],[c_43428,c_43957])).

tff(c_44007,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40030,c_43989])).

tff(c_44009,plain,(
    r1_tarski(k1_zfmisc_1(u1_struct_0('#skF_8')),k1_zfmisc_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_35855])).

tff(c_32214,plain,(
    ! [A_1407,A_1408,C_1409] :
      ( m1_subset_1(A_1407,A_1408)
      | ~ r2_hidden(A_1407,C_1409)
      | ~ r1_tarski(C_1409,A_1408) ) ),
    inference(resolution,[status(thm)],[c_100,c_16185])).

tff(c_32235,plain,(
    ! [C_13,A_1408,A_9] :
      ( m1_subset_1(C_13,A_1408)
      | ~ r1_tarski(k1_zfmisc_1(A_9),A_1408)
      | ~ r1_tarski(C_13,A_9) ) ),
    inference(resolution,[status(thm)],[c_18,c_32214])).

tff(c_35561,plain,(
    ! [C_1621,A_1622] :
      ( m1_subset_1(C_1621,k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ r1_tarski(C_1621,A_1622)
      | ~ r1_tarski(k1_zfmisc_1(A_1622),k1_zfmisc_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_33775,c_32235])).

tff(c_35598,plain,(
    ! [A_1] :
      ( m1_subset_1(A_1,k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ r1_tarski(k1_zfmisc_1(A_1),k1_zfmisc_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_259,c_35561])).

tff(c_44086,plain,(
    m1_subset_1(u1_struct_0('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_8'))) ),
    inference(resolution,[status(thm)],[c_44009,c_35598])).

tff(c_44073,plain,(
    ! [B_15] :
      ( r2_hidden(B_15,k1_zfmisc_1('#skF_9'))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0('#skF_8')))
      | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_8'))) ) ),
    inference(resolution,[status(thm)],[c_44009,c_272])).

tff(c_44329,plain,(
    ! [B_1875] :
      ( r2_hidden(B_1875,k1_zfmisc_1('#skF_9'))
      | ~ m1_subset_1(B_1875,k1_zfmisc_1(u1_struct_0('#skF_8'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_44073])).

tff(c_44414,plain,(
    r2_hidden(u1_struct_0('#skF_8'),k1_zfmisc_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_44086,c_44329])).

tff(c_44508,plain,(
    r1_tarski(u1_struct_0('#skF_8'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_44414,c_16])).

tff(c_44520,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35680,c_44508])).

tff(c_44522,plain,(
    r1_tarski(u1_struct_0('#skF_8'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_35678])).

tff(c_45217,plain,(
    ! [A_1898,B_1899,B_1900] :
      ( r2_hidden('#skF_3'(A_1898,B_1899),B_1900)
      | ~ r1_tarski(A_1898,B_1900)
      | r2_hidden('#skF_2'(A_1898,B_1899),B_1899)
      | B_1899 = A_1898 ) ),
    inference(resolution,[status(thm)],[c_32126,c_2])).

tff(c_45334,plain,(
    ! [A_1901,B_1902] :
      ( ~ r1_tarski(A_1901,B_1902)
      | r2_hidden('#skF_2'(A_1901,B_1902),B_1902)
      | B_1902 = A_1901 ) ),
    inference(resolution,[status(thm)],[c_45217,c_10])).

tff(c_45408,plain,(
    ! [A_1904,B_1905] :
      ( m1_subset_1('#skF_2'(A_1904,B_1905),B_1905)
      | ~ r1_tarski(A_1904,B_1905)
      | B_1905 = A_1904 ) ),
    inference(resolution,[status(thm)],[c_45334,c_36])).

tff(c_35647,plain,(
    ! [B_1624] :
      ( ~ r1_tarski(u1_struct_0('#skF_8'),B_1624)
      | u1_struct_0('#skF_8') = B_1624
      | ~ m1_subset_1('#skF_2'(u1_struct_0('#skF_8'),B_1624),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_35599,c_32587])).

tff(c_45412,plain,
    ( ~ r1_tarski(u1_struct_0('#skF_8'),'#skF_9')
    | u1_struct_0('#skF_8') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_45408,c_35647])).

tff(c_45452,plain,(
    u1_struct_0('#skF_8') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44522,c_45412])).

tff(c_45565,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45452,c_32125])).

tff(c_45577,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_45565])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:45:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.81/7.99  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.00/8.03  
% 16.00/8.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.00/8.03  %$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_2 > #skF_7 > #skF_1 > #skF_5 > #skF_4
% 16.00/8.03  
% 16.00/8.03  %Foreground sorts:
% 16.00/8.03  
% 16.00/8.03  
% 16.00/8.03  %Background operators:
% 16.00/8.03  
% 16.00/8.03  
% 16.00/8.03  %Foreground operators:
% 16.00/8.03  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 16.00/8.03  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 16.00/8.03  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 16.00/8.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.00/8.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.00/8.03  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 16.00/8.03  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 16.00/8.03  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 16.00/8.03  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 16.00/8.03  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 16.00/8.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.00/8.03  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 16.00/8.03  tff('#skF_9', type, '#skF_9': $i).
% 16.00/8.03  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 16.00/8.03  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.00/8.03  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 16.00/8.03  tff('#skF_8', type, '#skF_8': $i).
% 16.00/8.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.00/8.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.00/8.03  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 16.00/8.03  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 16.00/8.03  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 16.00/8.03  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 16.00/8.03  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 16.00/8.03  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 16.00/8.03  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 16.00/8.03  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 16.00/8.03  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 16.00/8.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.00/8.03  
% 16.00/8.06  tff(f_142, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_subset_1(B, u1_struct_0(A)) <=> ~r2_hidden(k3_yellow_0(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_7)).
% 16.00/8.06  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 16.00/8.06  tff(f_46, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 16.00/8.06  tff(f_63, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 16.00/8.06  tff(f_113, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 16.00/8.06  tff(f_59, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 16.00/8.06  tff(f_69, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 16.00/8.06  tff(f_73, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(k3_yellow_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow_0)).
% 16.00/8.06  tff(f_87, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, k3_yellow_0(A), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_yellow_0)).
% 16.00/8.06  tff(f_106, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v13_waybel_0(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r1_orders_2(A, C, D)) => r2_hidden(D, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_waybel_0)).
% 16.00/8.06  tff(f_39, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 16.00/8.06  tff(c_66, plain, (~v1_xboole_0('#skF_9')), inference(cnfTransformation, [status(thm)], [f_142])).
% 16.00/8.06  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 16.00/8.06  tff(c_246, plain, (![A_83, B_84]: (~r2_hidden('#skF_1'(A_83, B_84), B_84) | r1_tarski(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_32])).
% 16.00/8.06  tff(c_259, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_246])).
% 16.00/8.06  tff(c_96, plain, (![C_59, A_60]: (r2_hidden(C_59, k1_zfmisc_1(A_60)) | ~r1_tarski(C_59, A_60))), inference(cnfTransformation, [status(thm)], [f_46])).
% 16.00/8.06  tff(c_36, plain, (![A_16, B_17]: (m1_subset_1(A_16, B_17) | ~r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_63])).
% 16.00/8.06  tff(c_121, plain, (![C_65, A_66]: (m1_subset_1(C_65, k1_zfmisc_1(A_66)) | ~r1_tarski(C_65, A_66))), inference(resolution, [status(thm)], [c_96, c_36])).
% 16.00/8.06  tff(c_58, plain, (![B_51]: (~v1_subset_1(B_51, B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(B_51)))), inference(cnfTransformation, [status(thm)], [f_113])).
% 16.00/8.06  tff(c_130, plain, (![A_66]: (~v1_subset_1(A_66, A_66) | ~r1_tarski(A_66, A_66))), inference(resolution, [status(thm)], [c_121, c_58])).
% 16.00/8.06  tff(c_276, plain, (![A_66]: (~v1_subset_1(A_66, A_66))), inference(demodulation, [status(thm), theory('equality')], [c_259, c_130])).
% 16.00/8.06  tff(c_60, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(u1_struct_0('#skF_8')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 16.00/8.06  tff(c_106, plain, (![B_63, A_64]: (v1_xboole_0(B_63) | ~m1_subset_1(B_63, A_64) | ~v1_xboole_0(A_64))), inference(cnfTransformation, [status(thm)], [f_59])).
% 16.00/8.06  tff(c_115, plain, (v1_xboole_0('#skF_9') | ~v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_60, c_106])).
% 16.00/8.06  tff(c_120, plain, (~v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_66, c_115])).
% 16.00/8.06  tff(c_224, plain, (![B_79, A_80]: (r2_hidden(B_79, A_80) | ~m1_subset_1(B_79, A_80) | v1_xboole_0(A_80))), inference(cnfTransformation, [status(thm)], [f_59])).
% 16.00/8.06  tff(c_16, plain, (![C_13, A_9]: (r1_tarski(C_13, A_9) | ~r2_hidden(C_13, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 16.00/8.06  tff(c_16239, plain, (![B_769, A_770]: (r1_tarski(B_769, A_770) | ~m1_subset_1(B_769, k1_zfmisc_1(A_770)) | v1_xboole_0(k1_zfmisc_1(A_770)))), inference(resolution, [status(thm)], [c_224, c_16])).
% 16.00/8.06  tff(c_16257, plain, (r1_tarski('#skF_9', u1_struct_0('#skF_8')) | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_60, c_16239])).
% 16.00/8.06  tff(c_16264, plain, (r1_tarski('#skF_9', u1_struct_0('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_120, c_16257])).
% 16.00/8.06  tff(c_236, plain, (![A_81, B_82]: (r2_hidden('#skF_1'(A_81, B_82), A_81) | r1_tarski(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_32])).
% 16.00/8.06  tff(c_245, plain, (![A_81, B_82]: (m1_subset_1('#skF_1'(A_81, B_82), A_81) | r1_tarski(A_81, B_82))), inference(resolution, [status(thm)], [c_236, c_36])).
% 16.00/8.06  tff(c_16185, plain, (![A_756, C_757, B_758]: (m1_subset_1(A_756, C_757) | ~m1_subset_1(B_758, k1_zfmisc_1(C_757)) | ~r2_hidden(A_756, B_758))), inference(cnfTransformation, [status(thm)], [f_69])).
% 16.00/8.06  tff(c_16204, plain, (![A_759]: (m1_subset_1(A_759, u1_struct_0('#skF_8')) | ~r2_hidden(A_759, '#skF_9'))), inference(resolution, [status(thm)], [c_60, c_16185])).
% 16.00/8.06  tff(c_34, plain, (![B_15, A_14]: (v1_xboole_0(B_15) | ~m1_subset_1(B_15, A_14) | ~v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 16.00/8.06  tff(c_16208, plain, (![A_759]: (v1_xboole_0(A_759) | ~v1_xboole_0(u1_struct_0('#skF_8')) | ~r2_hidden(A_759, '#skF_9'))), inference(resolution, [status(thm)], [c_16204, c_34])).
% 16.00/8.06  tff(c_16209, plain, (~v1_xboole_0(u1_struct_0('#skF_8'))), inference(splitLeft, [status(thm)], [c_16208])).
% 16.00/8.06  tff(c_16203, plain, (![A_756]: (m1_subset_1(A_756, u1_struct_0('#skF_8')) | ~r2_hidden(A_756, '#skF_9'))), inference(resolution, [status(thm)], [c_60, c_16185])).
% 16.00/8.06  tff(c_262, plain, (![C_85, B_86, A_87]: (r2_hidden(C_85, B_86) | ~r2_hidden(C_85, A_87) | ~r1_tarski(A_87, B_86))), inference(cnfTransformation, [status(thm)], [f_32])).
% 16.00/8.06  tff(c_16509, plain, (![A_804, B_805, B_806]: (r2_hidden('#skF_1'(A_804, B_805), B_806) | ~r1_tarski(A_804, B_806) | r1_tarski(A_804, B_805))), inference(resolution, [status(thm)], [c_6, c_262])).
% 16.00/8.06  tff(c_30, plain, (![B_15, A_14]: (r2_hidden(B_15, A_14) | ~m1_subset_1(B_15, A_14) | v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 16.00/8.06  tff(c_16333, plain, (![A_780, A_781]: (r1_tarski(A_780, A_781) | ~m1_subset_1('#skF_1'(A_780, A_781), A_781) | v1_xboole_0(A_781))), inference(resolution, [status(thm)], [c_30, c_246])).
% 16.00/8.06  tff(c_16337, plain, (![A_780]: (r1_tarski(A_780, u1_struct_0('#skF_8')) | v1_xboole_0(u1_struct_0('#skF_8')) | ~r2_hidden('#skF_1'(A_780, u1_struct_0('#skF_8')), '#skF_9'))), inference(resolution, [status(thm)], [c_16203, c_16333])).
% 16.00/8.06  tff(c_16352, plain, (![A_780]: (r1_tarski(A_780, u1_struct_0('#skF_8')) | ~r2_hidden('#skF_1'(A_780, u1_struct_0('#skF_8')), '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_16209, c_16337])).
% 16.00/8.06  tff(c_16535, plain, (![A_807]: (~r1_tarski(A_807, '#skF_9') | r1_tarski(A_807, u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_16509, c_16352])).
% 16.00/8.06  tff(c_272, plain, (![B_15, B_86, A_14]: (r2_hidden(B_15, B_86) | ~r1_tarski(A_14, B_86) | ~m1_subset_1(B_15, A_14) | v1_xboole_0(A_14))), inference(resolution, [status(thm)], [c_30, c_262])).
% 16.00/8.06  tff(c_17695, plain, (![B_884, A_885]: (r2_hidden(B_884, u1_struct_0('#skF_8')) | ~m1_subset_1(B_884, A_885) | v1_xboole_0(A_885) | ~r1_tarski(A_885, '#skF_9'))), inference(resolution, [status(thm)], [c_16535, c_272])).
% 16.00/8.06  tff(c_17719, plain, (![A_756]: (r2_hidden(A_756, u1_struct_0('#skF_8')) | v1_xboole_0(u1_struct_0('#skF_8')) | ~r1_tarski(u1_struct_0('#skF_8'), '#skF_9') | ~r2_hidden(A_756, '#skF_9'))), inference(resolution, [status(thm)], [c_16203, c_17695])).
% 16.00/8.06  tff(c_17754, plain, (![A_756]: (r2_hidden(A_756, u1_struct_0('#skF_8')) | ~r1_tarski(u1_struct_0('#skF_8'), '#skF_9') | ~r2_hidden(A_756, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_16209, c_17719])).
% 16.00/8.06  tff(c_17767, plain, (~r1_tarski(u1_struct_0('#skF_8'), '#skF_9')), inference(splitLeft, [status(thm)], [c_17754])).
% 16.00/8.06  tff(c_62, plain, (v13_waybel_0('#skF_9', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_142])).
% 16.00/8.06  tff(c_133, plain, (![B_68, A_69]: (r2_hidden(B_68, A_69) | ~m1_subset_1(B_68, A_69) | v1_xboole_0(A_69))), inference(cnfTransformation, [status(thm)], [f_59])).
% 16.00/8.06  tff(c_86, plain, (v1_subset_1('#skF_9', u1_struct_0('#skF_8')) | ~r2_hidden(k3_yellow_0('#skF_8'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_142])).
% 16.00/8.06  tff(c_131, plain, (~r2_hidden(k3_yellow_0('#skF_8'), '#skF_9')), inference(splitLeft, [status(thm)], [c_86])).
% 16.00/8.06  tff(c_136, plain, (~m1_subset_1(k3_yellow_0('#skF_8'), '#skF_9') | v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_133, c_131])).
% 16.00/8.06  tff(c_146, plain, (~m1_subset_1(k3_yellow_0('#skF_8'), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_66, c_136])).
% 16.00/8.06  tff(c_68, plain, (l1_orders_2('#skF_8')), inference(cnfTransformation, [status(thm)], [f_142])).
% 16.00/8.06  tff(c_80, plain, (r2_hidden(k3_yellow_0('#skF_8'), '#skF_9') | ~v1_subset_1('#skF_9', u1_struct_0('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_142])).
% 16.00/8.06  tff(c_163, plain, (~v1_subset_1('#skF_9', u1_struct_0('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_131, c_80])).
% 16.00/8.06  tff(c_184, plain, (![B_76, A_77]: (v1_subset_1(B_76, A_77) | B_76=A_77 | ~m1_subset_1(B_76, k1_zfmisc_1(A_77)))), inference(cnfTransformation, [status(thm)], [f_113])).
% 16.00/8.06  tff(c_194, plain, (v1_subset_1('#skF_9', u1_struct_0('#skF_8')) | u1_struct_0('#skF_8')='#skF_9'), inference(resolution, [status(thm)], [c_60, c_184])).
% 16.00/8.06  tff(c_199, plain, (u1_struct_0('#skF_8')='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_163, c_194])).
% 16.00/8.06  tff(c_40, plain, (![A_21]: (m1_subset_1(k3_yellow_0(A_21), u1_struct_0(A_21)) | ~l1_orders_2(A_21))), inference(cnfTransformation, [status(thm)], [f_73])).
% 16.00/8.06  tff(c_206, plain, (m1_subset_1(k3_yellow_0('#skF_8'), '#skF_9') | ~l1_orders_2('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_199, c_40])).
% 16.00/8.06  tff(c_210, plain, (m1_subset_1(k3_yellow_0('#skF_8'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_206])).
% 16.00/8.06  tff(c_212, plain, $false, inference(negUnitSimplification, [status(thm)], [c_146, c_210])).
% 16.00/8.06  tff(c_214, plain, (r2_hidden(k3_yellow_0('#skF_8'), '#skF_9')), inference(splitRight, [status(thm)], [c_86])).
% 16.00/8.06  tff(c_78, plain, (~v2_struct_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_142])).
% 16.00/8.06  tff(c_72, plain, (v5_orders_2('#skF_8')), inference(cnfTransformation, [status(thm)], [f_142])).
% 16.00/8.06  tff(c_70, plain, (v1_yellow_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_142])).
% 16.00/8.06  tff(c_42, plain, (![A_22, B_24]: (r1_orders_2(A_22, k3_yellow_0(A_22), B_24) | ~m1_subset_1(B_24, u1_struct_0(A_22)) | ~l1_orders_2(A_22) | ~v1_yellow_0(A_22) | ~v5_orders_2(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_87])).
% 16.00/8.06  tff(c_18734, plain, (![D_941, B_942, A_943, C_944]: (r2_hidden(D_941, B_942) | ~r1_orders_2(A_943, C_944, D_941) | ~r2_hidden(C_944, B_942) | ~m1_subset_1(D_941, u1_struct_0(A_943)) | ~m1_subset_1(C_944, u1_struct_0(A_943)) | ~v13_waybel_0(B_942, A_943) | ~m1_subset_1(B_942, k1_zfmisc_1(u1_struct_0(A_943))) | ~l1_orders_2(A_943))), inference(cnfTransformation, [status(thm)], [f_106])).
% 16.00/8.06  tff(c_26014, plain, (![B_1195, B_1196, A_1197]: (r2_hidden(B_1195, B_1196) | ~r2_hidden(k3_yellow_0(A_1197), B_1196) | ~m1_subset_1(k3_yellow_0(A_1197), u1_struct_0(A_1197)) | ~v13_waybel_0(B_1196, A_1197) | ~m1_subset_1(B_1196, k1_zfmisc_1(u1_struct_0(A_1197))) | ~m1_subset_1(B_1195, u1_struct_0(A_1197)) | ~l1_orders_2(A_1197) | ~v1_yellow_0(A_1197) | ~v5_orders_2(A_1197) | v2_struct_0(A_1197))), inference(resolution, [status(thm)], [c_42, c_18734])).
% 16.00/8.06  tff(c_26025, plain, (![B_1195, B_1196]: (r2_hidden(B_1195, B_1196) | ~r2_hidden(k3_yellow_0('#skF_8'), B_1196) | ~v13_waybel_0(B_1196, '#skF_8') | ~m1_subset_1(B_1196, k1_zfmisc_1(u1_struct_0('#skF_8'))) | ~m1_subset_1(B_1195, u1_struct_0('#skF_8')) | ~l1_orders_2('#skF_8') | ~v1_yellow_0('#skF_8') | ~v5_orders_2('#skF_8') | v2_struct_0('#skF_8') | ~r2_hidden(k3_yellow_0('#skF_8'), '#skF_9'))), inference(resolution, [status(thm)], [c_16203, c_26014])).
% 16.00/8.06  tff(c_26048, plain, (![B_1195, B_1196]: (r2_hidden(B_1195, B_1196) | ~r2_hidden(k3_yellow_0('#skF_8'), B_1196) | ~v13_waybel_0(B_1196, '#skF_8') | ~m1_subset_1(B_1196, k1_zfmisc_1(u1_struct_0('#skF_8'))) | ~m1_subset_1(B_1195, u1_struct_0('#skF_8')) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_72, c_70, c_68, c_26025])).
% 16.00/8.06  tff(c_26217, plain, (![B_1201, B_1202]: (r2_hidden(B_1201, B_1202) | ~r2_hidden(k3_yellow_0('#skF_8'), B_1202) | ~v13_waybel_0(B_1202, '#skF_8') | ~m1_subset_1(B_1202, k1_zfmisc_1(u1_struct_0('#skF_8'))) | ~m1_subset_1(B_1201, u1_struct_0('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_78, c_26048])).
% 16.00/8.06  tff(c_26331, plain, (![B_1201]: (r2_hidden(B_1201, '#skF_9') | ~r2_hidden(k3_yellow_0('#skF_8'), '#skF_9') | ~v13_waybel_0('#skF_9', '#skF_8') | ~m1_subset_1(B_1201, u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_60, c_26217])).
% 16.00/8.06  tff(c_26386, plain, (![B_1203]: (r2_hidden(B_1203, '#skF_9') | ~m1_subset_1(B_1203, u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_214, c_26331])).
% 16.00/8.06  tff(c_26979, plain, (![B_1213]: (r2_hidden('#skF_1'(u1_struct_0('#skF_8'), B_1213), '#skF_9') | r1_tarski(u1_struct_0('#skF_8'), B_1213))), inference(resolution, [status(thm)], [c_245, c_26386])).
% 16.00/8.06  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 16.00/8.06  tff(c_27001, plain, (r1_tarski(u1_struct_0('#skF_8'), '#skF_9')), inference(resolution, [status(thm)], [c_26979, c_4])).
% 16.00/8.06  tff(c_27019, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17767, c_17767, c_27001])).
% 16.00/8.06  tff(c_27021, plain, (r1_tarski(u1_struct_0('#skF_8'), '#skF_9')), inference(splitRight, [status(thm)], [c_17754])).
% 16.00/8.06  tff(c_100, plain, (![C_59, A_60]: (m1_subset_1(C_59, k1_zfmisc_1(A_60)) | ~r1_tarski(C_59, A_60))), inference(resolution, [status(thm)], [c_96, c_36])).
% 16.00/8.06  tff(c_16218, plain, (![A_763, A_764, C_765]: (m1_subset_1(A_763, A_764) | ~r2_hidden(A_763, C_765) | ~r1_tarski(C_765, A_764))), inference(resolution, [status(thm)], [c_100, c_16185])).
% 16.00/8.06  tff(c_16231, plain, (![B_15, A_764, A_14]: (m1_subset_1(B_15, A_764) | ~r1_tarski(A_14, A_764) | ~m1_subset_1(B_15, A_14) | v1_xboole_0(A_14))), inference(resolution, [status(thm)], [c_30, c_16218])).
% 16.00/8.06  tff(c_27037, plain, (![B_15]: (m1_subset_1(B_15, '#skF_9') | ~m1_subset_1(B_15, u1_struct_0('#skF_8')) | v1_xboole_0(u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_27021, c_16231])).
% 16.00/8.06  tff(c_27255, plain, (![B_1217]: (m1_subset_1(B_1217, '#skF_9') | ~m1_subset_1(B_1217, u1_struct_0('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_16209, c_27037])).
% 16.00/8.06  tff(c_27325, plain, (![B_82]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_8'), B_82), '#skF_9') | r1_tarski(u1_struct_0('#skF_8'), B_82))), inference(resolution, [status(thm)], [c_245, c_27255])).
% 16.00/8.06  tff(c_16409, plain, (![B_793, B_794, A_795]: (r2_hidden(B_793, B_794) | ~r1_tarski(A_795, B_794) | ~m1_subset_1(B_793, A_795) | v1_xboole_0(A_795))), inference(resolution, [status(thm)], [c_30, c_262])).
% 16.00/8.06  tff(c_16413, plain, (![B_793]: (r2_hidden(B_793, u1_struct_0('#skF_8')) | ~m1_subset_1(B_793, '#skF_9') | v1_xboole_0('#skF_9'))), inference(resolution, [status(thm)], [c_16264, c_16409])).
% 16.00/8.06  tff(c_16425, plain, (![B_796]: (r2_hidden(B_796, u1_struct_0('#skF_8')) | ~m1_subset_1(B_796, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_66, c_16413])).
% 16.00/8.06  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 16.00/8.06  tff(c_16447, plain, (![B_796, B_2]: (r2_hidden(B_796, B_2) | ~r1_tarski(u1_struct_0('#skF_8'), B_2) | ~m1_subset_1(B_796, '#skF_9'))), inference(resolution, [status(thm)], [c_16425, c_2])).
% 16.00/8.06  tff(c_27078, plain, (![B_1214]: (r2_hidden(B_1214, '#skF_9') | ~m1_subset_1(B_1214, '#skF_9'))), inference(resolution, [status(thm)], [c_27021, c_16447])).
% 16.00/8.06  tff(c_27415, plain, (![B_1226, B_1227]: (r2_hidden(B_1226, B_1227) | ~r1_tarski('#skF_9', B_1227) | ~m1_subset_1(B_1226, '#skF_9'))), inference(resolution, [status(thm)], [c_27078, c_2])).
% 16.00/8.06  tff(c_27644, plain, (![A_1240, B_1241]: (r1_tarski(A_1240, B_1241) | ~r1_tarski('#skF_9', B_1241) | ~m1_subset_1('#skF_1'(A_1240, B_1241), '#skF_9'))), inference(resolution, [status(thm)], [c_27415, c_4])).
% 16.00/8.06  tff(c_27659, plain, (![B_82]: (~r1_tarski('#skF_9', B_82) | r1_tarski(u1_struct_0('#skF_8'), B_82))), inference(resolution, [status(thm)], [c_27325, c_27644])).
% 16.00/8.06  tff(c_244, plain, (![A_9, B_82]: (r1_tarski('#skF_1'(k1_zfmisc_1(A_9), B_82), A_9) | r1_tarski(k1_zfmisc_1(A_9), B_82))), inference(resolution, [status(thm)], [c_236, c_16])).
% 16.00/8.06  tff(c_16534, plain, (![A_804, B_805, B_806]: (m1_subset_1('#skF_1'(A_804, B_805), B_806) | ~r1_tarski(A_804, B_806) | r1_tarski(A_804, B_805))), inference(resolution, [status(thm)], [c_16509, c_36])).
% 16.00/8.06  tff(c_27043, plain, (![B_15]: (r2_hidden(B_15, '#skF_9') | ~m1_subset_1(B_15, u1_struct_0('#skF_8')) | v1_xboole_0(u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_27021, c_272])).
% 16.00/8.06  tff(c_27177, plain, (![B_1216]: (r2_hidden(B_1216, '#skF_9') | ~m1_subset_1(B_1216, u1_struct_0('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_16209, c_27043])).
% 16.00/8.06  tff(c_28560, plain, (![A_1281, B_1282]: (r2_hidden('#skF_1'(A_1281, B_1282), '#skF_9') | ~r1_tarski(A_1281, u1_struct_0('#skF_8')) | r1_tarski(A_1281, B_1282))), inference(resolution, [status(thm)], [c_16534, c_27177])).
% 16.00/8.06  tff(c_28592, plain, (![A_1283]: (~r1_tarski(A_1283, u1_struct_0('#skF_8')) | r1_tarski(A_1283, '#skF_9'))), inference(resolution, [status(thm)], [c_28560, c_4])).
% 16.00/8.06  tff(c_29430, plain, (![B_1320]: (r1_tarski('#skF_1'(k1_zfmisc_1(u1_struct_0('#skF_8')), B_1320), '#skF_9') | r1_tarski(k1_zfmisc_1(u1_struct_0('#skF_8')), B_1320))), inference(resolution, [status(thm)], [c_244, c_28592])).
% 16.00/8.06  tff(c_18, plain, (![C_13, A_9]: (r2_hidden(C_13, k1_zfmisc_1(A_9)) | ~r1_tarski(C_13, A_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 16.00/8.06  tff(c_261, plain, (![A_83, A_9]: (r1_tarski(A_83, k1_zfmisc_1(A_9)) | ~r1_tarski('#skF_1'(A_83, k1_zfmisc_1(A_9)), A_9))), inference(resolution, [status(thm)], [c_18, c_246])).
% 16.00/8.06  tff(c_29480, plain, (r1_tarski(k1_zfmisc_1(u1_struct_0('#skF_8')), k1_zfmisc_1('#skF_9'))), inference(resolution, [status(thm)], [c_29430, c_261])).
% 16.00/8.06  tff(c_16233, plain, (![C_13, A_764, A_9]: (m1_subset_1(C_13, A_764) | ~r1_tarski(k1_zfmisc_1(A_9), A_764) | ~r1_tarski(C_13, A_9))), inference(resolution, [status(thm)], [c_18, c_16218])).
% 16.00/8.06  tff(c_29679, plain, (![C_1324]: (m1_subset_1(C_1324, k1_zfmisc_1('#skF_9')) | ~r1_tarski(C_1324, u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_29480, c_16233])).
% 16.00/8.06  tff(c_29690, plain, (m1_subset_1(u1_struct_0('#skF_8'), k1_zfmisc_1('#skF_9')) | ~r1_tarski('#skF_9', u1_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_27659, c_29679])).
% 16.00/8.06  tff(c_29721, plain, (m1_subset_1(u1_struct_0('#skF_8'), k1_zfmisc_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_16264, c_29690])).
% 16.00/8.06  tff(c_56, plain, (![B_51, A_50]: (v1_subset_1(B_51, A_50) | B_51=A_50 | ~m1_subset_1(B_51, k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_113])).
% 16.00/8.06  tff(c_29791, plain, (v1_subset_1(u1_struct_0('#skF_8'), '#skF_9') | u1_struct_0('#skF_8')='#skF_9'), inference(resolution, [status(thm)], [c_29721, c_56])).
% 16.00/8.06  tff(c_29963, plain, (u1_struct_0('#skF_8')='#skF_9'), inference(splitLeft, [status(thm)], [c_29791])).
% 16.00/8.06  tff(c_213, plain, (v1_subset_1('#skF_9', u1_struct_0('#skF_8'))), inference(splitRight, [status(thm)], [c_86])).
% 16.00/8.06  tff(c_30052, plain, (v1_subset_1('#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_29963, c_213])).
% 16.00/8.06  tff(c_30064, plain, $false, inference(negUnitSimplification, [status(thm)], [c_276, c_30052])).
% 16.00/8.06  tff(c_30066, plain, (u1_struct_0('#skF_8')!='#skF_9'), inference(splitRight, [status(thm)], [c_29791])).
% 16.00/8.06  tff(c_16471, plain, (![A_802, B_803]: (r2_hidden('#skF_2'(A_802, B_803), B_803) | r2_hidden('#skF_3'(A_802, B_803), A_802) | B_803=A_802)), inference(cnfTransformation, [status(thm)], [f_39])).
% 16.00/8.06  tff(c_30982, plain, (![A_1359, B_1360, B_1361]: (r2_hidden('#skF_3'(A_1359, B_1360), B_1361) | ~r1_tarski(A_1359, B_1361) | r2_hidden('#skF_2'(A_1359, B_1360), B_1360) | B_1360=A_1359)), inference(resolution, [status(thm)], [c_16471, c_2])).
% 16.00/8.06  tff(c_10, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), B_7) | ~r2_hidden('#skF_3'(A_6, B_7), B_7) | B_7=A_6)), inference(cnfTransformation, [status(thm)], [f_39])).
% 16.00/8.06  tff(c_31082, plain, (![A_1362, B_1363]: (~r1_tarski(A_1362, B_1363) | r2_hidden('#skF_2'(A_1362, B_1363), B_1363) | B_1363=A_1362)), inference(resolution, [status(thm)], [c_30982, c_10])).
% 16.00/8.06  tff(c_16201, plain, (![A_756, A_60, C_59]: (m1_subset_1(A_756, A_60) | ~r2_hidden(A_756, C_59) | ~r1_tarski(C_59, A_60))), inference(resolution, [status(thm)], [c_100, c_16185])).
% 16.00/8.06  tff(c_31988, plain, (![A_1397, B_1398, A_1399]: (m1_subset_1('#skF_2'(A_1397, B_1398), A_1399) | ~r1_tarski(B_1398, A_1399) | ~r1_tarski(A_1397, B_1398) | B_1398=A_1397)), inference(resolution, [status(thm)], [c_31082, c_16201])).
% 16.00/8.06  tff(c_16724, plain, (![A_822, B_823]: (~r2_hidden('#skF_2'(A_822, B_823), A_822) | r2_hidden('#skF_3'(A_822, B_823), A_822) | B_823=A_822)), inference(cnfTransformation, [status(thm)], [f_39])).
% 16.00/8.06  tff(c_16758, plain, (![A_822, B_823]: (m1_subset_1('#skF_3'(A_822, B_823), A_822) | ~r2_hidden('#skF_2'(A_822, B_823), A_822) | B_823=A_822)), inference(resolution, [status(thm)], [c_16724, c_36])).
% 16.00/8.06  tff(c_28272, plain, (![B_1265]: (m1_subset_1('#skF_3'('#skF_9', B_1265), '#skF_9') | B_1265='#skF_9' | ~m1_subset_1('#skF_2'('#skF_9', B_1265), '#skF_9'))), inference(resolution, [status(thm)], [c_27078, c_16758])).
% 16.00/8.06  tff(c_16564, plain, (![B_15, A_807]: (r2_hidden(B_15, u1_struct_0('#skF_8')) | ~m1_subset_1(B_15, A_807) | v1_xboole_0(A_807) | ~r1_tarski(A_807, '#skF_9'))), inference(resolution, [status(thm)], [c_16535, c_272])).
% 16.00/8.06  tff(c_28274, plain, (![B_1265]: (r2_hidden('#skF_3'('#skF_9', B_1265), u1_struct_0('#skF_8')) | v1_xboole_0('#skF_9') | ~r1_tarski('#skF_9', '#skF_9') | B_1265='#skF_9' | ~m1_subset_1('#skF_2'('#skF_9', B_1265), '#skF_9'))), inference(resolution, [status(thm)], [c_28272, c_16564])).
% 16.00/8.06  tff(c_28282, plain, (![B_1265]: (r2_hidden('#skF_3'('#skF_9', B_1265), u1_struct_0('#skF_8')) | v1_xboole_0('#skF_9') | B_1265='#skF_9' | ~m1_subset_1('#skF_2'('#skF_9', B_1265), '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_259, c_28274])).
% 16.00/8.06  tff(c_28283, plain, (![B_1265]: (r2_hidden('#skF_3'('#skF_9', B_1265), u1_struct_0('#skF_8')) | B_1265='#skF_9' | ~m1_subset_1('#skF_2'('#skF_9', B_1265), '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_66, c_28282])).
% 16.00/8.06  tff(c_8, plain, (![A_6, B_7]: (~r2_hidden('#skF_2'(A_6, B_7), A_6) | ~r2_hidden('#skF_3'(A_6, B_7), B_7) | B_7=A_6)), inference(cnfTransformation, [status(thm)], [f_39])).
% 16.00/8.06  tff(c_28316, plain, (![B_1267]: (~r2_hidden('#skF_3'('#skF_9', B_1267), B_1267) | B_1267='#skF_9' | ~m1_subset_1('#skF_2'('#skF_9', B_1267), '#skF_9'))), inference(resolution, [status(thm)], [c_27078, c_8])).
% 16.00/8.06  tff(c_28369, plain, (u1_struct_0('#skF_8')='#skF_9' | ~m1_subset_1('#skF_2'('#skF_9', u1_struct_0('#skF_8')), '#skF_9')), inference(resolution, [status(thm)], [c_28283, c_28316])).
% 16.00/8.06  tff(c_28385, plain, (~m1_subset_1('#skF_2'('#skF_9', u1_struct_0('#skF_8')), '#skF_9')), inference(splitLeft, [status(thm)], [c_28369])).
% 16.00/8.06  tff(c_32003, plain, (~r1_tarski(u1_struct_0('#skF_8'), '#skF_9') | ~r1_tarski('#skF_9', u1_struct_0('#skF_8')) | u1_struct_0('#skF_8')='#skF_9'), inference(resolution, [status(thm)], [c_31988, c_28385])).
% 16.00/8.06  tff(c_32044, plain, (u1_struct_0('#skF_8')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_16264, c_27021, c_32003])).
% 16.00/8.06  tff(c_32046, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30066, c_32044])).
% 16.00/8.06  tff(c_32047, plain, (u1_struct_0('#skF_8')='#skF_9'), inference(splitRight, [status(thm)], [c_28369])).
% 16.00/8.06  tff(c_32113, plain, (v1_subset_1('#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_32047, c_213])).
% 16.00/8.06  tff(c_32123, plain, $false, inference(negUnitSimplification, [status(thm)], [c_276, c_32113])).
% 16.00/8.06  tff(c_32125, plain, (v1_xboole_0(u1_struct_0('#skF_8'))), inference(splitRight, [status(thm)], [c_16208])).
% 16.00/8.06  tff(c_32126, plain, (![A_1400, B_1401]: (r2_hidden('#skF_2'(A_1400, B_1401), B_1401) | r2_hidden('#skF_3'(A_1400, B_1401), A_1400) | B_1401=A_1400)), inference(cnfTransformation, [status(thm)], [f_39])).
% 16.00/8.06  tff(c_33234, plain, (![A_1505, B_1506]: (m1_subset_1('#skF_3'(A_1505, B_1506), A_1505) | r2_hidden('#skF_2'(A_1505, B_1506), B_1506) | B_1506=A_1505)), inference(resolution, [status(thm)], [c_32126, c_36])).
% 16.00/8.06  tff(c_35276, plain, (![A_1609, B_1610]: (v1_xboole_0('#skF_3'(A_1609, B_1610)) | ~v1_xboole_0(A_1609) | r2_hidden('#skF_2'(A_1609, B_1610), B_1610) | B_1610=A_1609)), inference(resolution, [status(thm)], [c_33234, c_34])).
% 16.00/8.06  tff(c_35334, plain, (![A_1609, B_1610]: (m1_subset_1('#skF_2'(A_1609, B_1610), B_1610) | v1_xboole_0('#skF_3'(A_1609, B_1610)) | ~v1_xboole_0(A_1609) | B_1610=A_1609)), inference(resolution, [status(thm)], [c_35276, c_36])).
% 16.00/8.06  tff(c_32236, plain, (![B_1410, A_1411]: (r1_tarski(B_1410, A_1411) | ~m1_subset_1(B_1410, k1_zfmisc_1(A_1411)) | v1_xboole_0(k1_zfmisc_1(A_1411)))), inference(resolution, [status(thm)], [c_224, c_16])).
% 16.00/8.06  tff(c_32254, plain, (r1_tarski('#skF_9', u1_struct_0('#skF_8')) | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_60, c_32236])).
% 16.00/8.06  tff(c_32261, plain, (r1_tarski('#skF_9', u1_struct_0('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_120, c_32254])).
% 16.00/8.06  tff(c_32540, plain, (![B_1446, B_1447, A_1448]: (r2_hidden(B_1446, B_1447) | ~r1_tarski(A_1448, B_1447) | ~m1_subset_1(B_1446, A_1448) | v1_xboole_0(A_1448))), inference(resolution, [status(thm)], [c_30, c_262])).
% 16.00/8.06  tff(c_32544, plain, (![B_1446]: (r2_hidden(B_1446, u1_struct_0('#skF_8')) | ~m1_subset_1(B_1446, '#skF_9') | v1_xboole_0('#skF_9'))), inference(resolution, [status(thm)], [c_32261, c_32540])).
% 16.00/8.06  tff(c_32552, plain, (![B_1446]: (r2_hidden(B_1446, u1_struct_0('#skF_8')) | ~m1_subset_1(B_1446, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_66, c_32544])).
% 16.00/8.06  tff(c_32371, plain, (![A_1426, B_1427]: (~r2_hidden('#skF_2'(A_1426, B_1427), A_1426) | r2_hidden('#skF_3'(A_1426, B_1427), A_1426) | B_1427=A_1426)), inference(cnfTransformation, [status(thm)], [f_39])).
% 16.00/8.06  tff(c_35512, plain, (![A_1618, B_1619, B_1620]: (r2_hidden('#skF_3'(A_1618, B_1619), B_1620) | ~r1_tarski(A_1618, B_1620) | ~r2_hidden('#skF_2'(A_1618, B_1619), A_1618) | B_1619=A_1618)), inference(resolution, [status(thm)], [c_32371, c_2])).
% 16.00/8.06  tff(c_35599, plain, (![B_1623, B_1624]: (r2_hidden('#skF_3'(u1_struct_0('#skF_8'), B_1623), B_1624) | ~r1_tarski(u1_struct_0('#skF_8'), B_1624) | u1_struct_0('#skF_8')=B_1623 | ~m1_subset_1('#skF_2'(u1_struct_0('#skF_8'), B_1623), '#skF_9'))), inference(resolution, [status(thm)], [c_32552, c_35512])).
% 16.00/8.06  tff(c_32566, plain, (![B_1451]: (r2_hidden(B_1451, u1_struct_0('#skF_8')) | ~m1_subset_1(B_1451, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_66, c_32544])).
% 16.00/8.06  tff(c_32587, plain, (![B_7]: (~r2_hidden('#skF_3'(u1_struct_0('#skF_8'), B_7), B_7) | u1_struct_0('#skF_8')=B_7 | ~m1_subset_1('#skF_2'(u1_struct_0('#skF_8'), B_7), '#skF_9'))), inference(resolution, [status(thm)], [c_32566, c_8])).
% 16.00/8.06  tff(c_35664, plain, (![B_1626]: (~r1_tarski(u1_struct_0('#skF_8'), B_1626) | u1_struct_0('#skF_8')=B_1626 | ~m1_subset_1('#skF_2'(u1_struct_0('#skF_8'), B_1626), '#skF_9'))), inference(resolution, [status(thm)], [c_35599, c_32587])).
% 16.00/8.06  tff(c_35668, plain, (~r1_tarski(u1_struct_0('#skF_8'), '#skF_9') | v1_xboole_0('#skF_3'(u1_struct_0('#skF_8'), '#skF_9')) | ~v1_xboole_0(u1_struct_0('#skF_8')) | u1_struct_0('#skF_8')='#skF_9'), inference(resolution, [status(thm)], [c_35334, c_35664])).
% 16.00/8.06  tff(c_35678, plain, (~r1_tarski(u1_struct_0('#skF_8'), '#skF_9') | v1_xboole_0('#skF_3'(u1_struct_0('#skF_8'), '#skF_9')) | u1_struct_0('#skF_8')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_32125, c_35668])).
% 16.00/8.06  tff(c_35680, plain, (~r1_tarski(u1_struct_0('#skF_8'), '#skF_9')), inference(splitLeft, [status(thm)], [c_35678])).
% 16.00/8.06  tff(c_33135, plain, (![A_1501, B_1502]: (m1_subset_1('#skF_3'(A_1501, B_1502), A_1501) | ~r2_hidden('#skF_2'(A_1501, B_1502), A_1501) | B_1502=A_1501)), inference(resolution, [status(thm)], [c_32371, c_36])).
% 16.00/8.06  tff(c_33409, plain, (![B_1515]: (m1_subset_1('#skF_3'(u1_struct_0('#skF_8'), B_1515), u1_struct_0('#skF_8')) | u1_struct_0('#skF_8')=B_1515 | ~m1_subset_1('#skF_2'(u1_struct_0('#skF_8'), B_1515), '#skF_9'))), inference(resolution, [status(thm)], [c_32552, c_33135])).
% 16.00/8.06  tff(c_33412, plain, (![B_1515]: (v1_xboole_0('#skF_3'(u1_struct_0('#skF_8'), B_1515)) | ~v1_xboole_0(u1_struct_0('#skF_8')) | u1_struct_0('#skF_8')=B_1515 | ~m1_subset_1('#skF_2'(u1_struct_0('#skF_8'), B_1515), '#skF_9'))), inference(resolution, [status(thm)], [c_33409, c_34])).
% 16.00/8.06  tff(c_38698, plain, (![B_1753]: (v1_xboole_0('#skF_3'(u1_struct_0('#skF_8'), B_1753)) | u1_struct_0('#skF_8')=B_1753 | ~m1_subset_1('#skF_2'(u1_struct_0('#skF_8'), B_1753), '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_32125, c_33412])).
% 16.00/8.06  tff(c_38714, plain, (v1_xboole_0('#skF_3'(u1_struct_0('#skF_8'), '#skF_9')) | ~v1_xboole_0(u1_struct_0('#skF_8')) | u1_struct_0('#skF_8')='#skF_9'), inference(resolution, [status(thm)], [c_35334, c_38698])).
% 16.00/8.06  tff(c_38727, plain, (v1_xboole_0('#skF_3'(u1_struct_0('#skF_8'), '#skF_9')) | u1_struct_0('#skF_8')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_32125, c_38714])).
% 16.00/8.06  tff(c_38729, plain, (u1_struct_0('#skF_8')='#skF_9'), inference(splitLeft, [status(thm)], [c_38727])).
% 16.00/8.06  tff(c_32506, plain, (![A_1441, B_1442, B_1443]: (r2_hidden('#skF_1'(A_1441, B_1442), B_1443) | ~r1_tarski(A_1441, B_1443) | r1_tarski(A_1441, B_1442))), inference(resolution, [status(thm)], [c_6, c_262])).
% 16.00/8.06  tff(c_32537, plain, (![A_1441, B_1442, A_9]: (r1_tarski('#skF_1'(A_1441, B_1442), A_9) | ~r1_tarski(A_1441, k1_zfmisc_1(A_9)) | r1_tarski(A_1441, B_1442))), inference(resolution, [status(thm)], [c_32506, c_16])).
% 16.00/8.06  tff(c_32631, plain, (![A_1460, B_1461, B_1462]: (m1_subset_1('#skF_1'(A_1460, B_1461), B_1462) | ~r1_tarski(A_1460, B_1462) | r1_tarski(A_1460, B_1461))), inference(resolution, [status(thm)], [c_32506, c_36])).
% 16.00/8.06  tff(c_32594, plain, (![A_1]: (r1_tarski(A_1, u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_1'(A_1, u1_struct_0('#skF_8')), '#skF_9'))), inference(resolution, [status(thm)], [c_32566, c_4])).
% 16.00/8.06  tff(c_32665, plain, (![A_1463]: (~r1_tarski(A_1463, '#skF_9') | r1_tarski(A_1463, u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_32631, c_32594])).
% 16.00/8.06  tff(c_33631, plain, (![A_1534]: (r1_tarski(A_1534, k1_zfmisc_1(u1_struct_0('#skF_8'))) | ~r1_tarski('#skF_1'(A_1534, k1_zfmisc_1(u1_struct_0('#skF_8'))), '#skF_9'))), inference(resolution, [status(thm)], [c_32665, c_261])).
% 16.00/8.06  tff(c_33775, plain, (![A_1538]: (~r1_tarski(A_1538, k1_zfmisc_1('#skF_9')) | r1_tarski(A_1538, k1_zfmisc_1(u1_struct_0('#skF_8'))))), inference(resolution, [status(thm)], [c_32537, c_33631])).
% 16.00/8.06  tff(c_274, plain, (![C_13, B_86, A_9]: (r2_hidden(C_13, B_86) | ~r1_tarski(k1_zfmisc_1(A_9), B_86) | ~r1_tarski(C_13, A_9))), inference(resolution, [status(thm)], [c_18, c_262])).
% 16.00/8.06  tff(c_35818, plain, (![C_1631, A_1632]: (r2_hidden(C_1631, k1_zfmisc_1(u1_struct_0('#skF_8'))) | ~r1_tarski(C_1631, A_1632) | ~r1_tarski(k1_zfmisc_1(A_1632), k1_zfmisc_1('#skF_9')))), inference(resolution, [status(thm)], [c_33775, c_274])).
% 16.00/8.06  tff(c_35855, plain, (r2_hidden('#skF_9', k1_zfmisc_1(u1_struct_0('#skF_8'))) | ~r1_tarski(k1_zfmisc_1(u1_struct_0('#skF_8')), k1_zfmisc_1('#skF_9'))), inference(resolution, [status(thm)], [c_32261, c_35818])).
% 16.00/8.06  tff(c_35935, plain, (~r1_tarski(k1_zfmisc_1(u1_struct_0('#skF_8')), k1_zfmisc_1('#skF_9'))), inference(splitLeft, [status(thm)], [c_35855])).
% 16.00/8.06  tff(c_38746, plain, (~r1_tarski(k1_zfmisc_1('#skF_9'), k1_zfmisc_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_38729, c_35935])).
% 16.00/8.06  tff(c_38823, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_259, c_38746])).
% 16.00/8.06  tff(c_38825, plain, (u1_struct_0('#skF_8')!='#skF_9'), inference(splitRight, [status(thm)], [c_38727])).
% 16.00/8.06  tff(c_33169, plain, (![A_1503, B_1504]: (m1_subset_1('#skF_2'(A_1503, B_1504), B_1504) | r2_hidden('#skF_3'(A_1503, B_1504), A_1503) | B_1504=A_1503)), inference(resolution, [status(thm)], [c_32126, c_36])).
% 16.00/8.06  tff(c_33333, plain, (![A_1510, B_1511]: (m1_subset_1('#skF_3'(A_1510, B_1511), A_1510) | m1_subset_1('#skF_2'(A_1510, B_1511), B_1511) | B_1511=A_1510)), inference(resolution, [status(thm)], [c_33169, c_36])).
% 16.00/8.06  tff(c_33378, plain, (![A_1510, B_1511]: (v1_xboole_0('#skF_2'(A_1510, B_1511)) | ~v1_xboole_0(B_1511) | m1_subset_1('#skF_3'(A_1510, B_1511), A_1510) | B_1511=A_1510)), inference(resolution, [status(thm)], [c_33333, c_34])).
% 16.00/8.06  tff(c_33105, plain, (![A_1498]: (r2_hidden('#skF_2'(A_1498, u1_struct_0('#skF_8')), u1_struct_0('#skF_8')) | u1_struct_0('#skF_8')=A_1498 | ~m1_subset_1('#skF_3'(A_1498, u1_struct_0('#skF_8')), '#skF_9'))), inference(resolution, [status(thm)], [c_32566, c_10])).
% 16.00/8.06  tff(c_39968, plain, (![A_1785]: (m1_subset_1('#skF_2'(A_1785, u1_struct_0('#skF_8')), u1_struct_0('#skF_8')) | u1_struct_0('#skF_8')=A_1785 | ~m1_subset_1('#skF_3'(A_1785, u1_struct_0('#skF_8')), '#skF_9'))), inference(resolution, [status(thm)], [c_33105, c_36])).
% 16.00/8.06  tff(c_39984, plain, (![A_1785]: (v1_xboole_0('#skF_2'(A_1785, u1_struct_0('#skF_8'))) | ~v1_xboole_0(u1_struct_0('#skF_8')) | u1_struct_0('#skF_8')=A_1785 | ~m1_subset_1('#skF_3'(A_1785, u1_struct_0('#skF_8')), '#skF_9'))), inference(resolution, [status(thm)], [c_39968, c_34])).
% 16.00/8.06  tff(c_40001, plain, (![A_1786]: (v1_xboole_0('#skF_2'(A_1786, u1_struct_0('#skF_8'))) | u1_struct_0('#skF_8')=A_1786 | ~m1_subset_1('#skF_3'(A_1786, u1_struct_0('#skF_8')), '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_32125, c_39984])).
% 16.00/8.06  tff(c_40013, plain, (v1_xboole_0('#skF_2'('#skF_9', u1_struct_0('#skF_8'))) | ~v1_xboole_0(u1_struct_0('#skF_8')) | u1_struct_0('#skF_8')='#skF_9'), inference(resolution, [status(thm)], [c_33378, c_40001])).
% 16.00/8.06  tff(c_40029, plain, (v1_xboole_0('#skF_2'('#skF_9', u1_struct_0('#skF_8'))) | u1_struct_0('#skF_8')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_32125, c_40013])).
% 16.00/8.06  tff(c_40030, plain, (v1_xboole_0('#skF_2'('#skF_9', u1_struct_0('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_38825, c_40029])).
% 16.00/8.06  tff(c_32, plain, (![B_15, A_14]: (m1_subset_1(B_15, A_14) | ~v1_xboole_0(B_15) | ~v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 16.00/8.06  tff(c_34642, plain, (![D_1577, B_1578, A_1579, C_1580]: (r2_hidden(D_1577, B_1578) | ~r1_orders_2(A_1579, C_1580, D_1577) | ~r2_hidden(C_1580, B_1578) | ~m1_subset_1(D_1577, u1_struct_0(A_1579)) | ~m1_subset_1(C_1580, u1_struct_0(A_1579)) | ~v13_waybel_0(B_1578, A_1579) | ~m1_subset_1(B_1578, k1_zfmisc_1(u1_struct_0(A_1579))) | ~l1_orders_2(A_1579))), inference(cnfTransformation, [status(thm)], [f_106])).
% 16.00/8.06  tff(c_42414, plain, (![B_1848, B_1849, A_1850]: (r2_hidden(B_1848, B_1849) | ~r2_hidden(k3_yellow_0(A_1850), B_1849) | ~m1_subset_1(k3_yellow_0(A_1850), u1_struct_0(A_1850)) | ~v13_waybel_0(B_1849, A_1850) | ~m1_subset_1(B_1849, k1_zfmisc_1(u1_struct_0(A_1850))) | ~m1_subset_1(B_1848, u1_struct_0(A_1850)) | ~l1_orders_2(A_1850) | ~v1_yellow_0(A_1850) | ~v5_orders_2(A_1850) | v2_struct_0(A_1850))), inference(resolution, [status(thm)], [c_42, c_34642])).
% 16.00/8.06  tff(c_42428, plain, (![B_1848, B_1849]: (r2_hidden(B_1848, B_1849) | ~r2_hidden(k3_yellow_0('#skF_8'), B_1849) | ~v13_waybel_0(B_1849, '#skF_8') | ~m1_subset_1(B_1849, k1_zfmisc_1(u1_struct_0('#skF_8'))) | ~m1_subset_1(B_1848, u1_struct_0('#skF_8')) | ~l1_orders_2('#skF_8') | ~v1_yellow_0('#skF_8') | ~v5_orders_2('#skF_8') | v2_struct_0('#skF_8') | ~r2_hidden(k3_yellow_0('#skF_8'), '#skF_9'))), inference(resolution, [status(thm)], [c_16203, c_42414])).
% 16.00/8.06  tff(c_42455, plain, (![B_1848, B_1849]: (r2_hidden(B_1848, B_1849) | ~r2_hidden(k3_yellow_0('#skF_8'), B_1849) | ~v13_waybel_0(B_1849, '#skF_8') | ~m1_subset_1(B_1849, k1_zfmisc_1(u1_struct_0('#skF_8'))) | ~m1_subset_1(B_1848, u1_struct_0('#skF_8')) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_72, c_70, c_68, c_42428])).
% 16.00/8.06  tff(c_42861, plain, (![B_1860, B_1861]: (r2_hidden(B_1860, B_1861) | ~r2_hidden(k3_yellow_0('#skF_8'), B_1861) | ~v13_waybel_0(B_1861, '#skF_8') | ~m1_subset_1(B_1861, k1_zfmisc_1(u1_struct_0('#skF_8'))) | ~m1_subset_1(B_1860, u1_struct_0('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_78, c_42455])).
% 16.00/8.06  tff(c_42993, plain, (![B_1860]: (r2_hidden(B_1860, '#skF_9') | ~r2_hidden(k3_yellow_0('#skF_8'), '#skF_9') | ~v13_waybel_0('#skF_9', '#skF_8') | ~m1_subset_1(B_1860, u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_60, c_42861])).
% 16.00/8.06  tff(c_43046, plain, (![B_1862]: (r2_hidden(B_1862, '#skF_9') | ~m1_subset_1(B_1862, u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_214, c_42993])).
% 16.00/8.06  tff(c_43254, plain, (![B_15]: (r2_hidden(B_15, '#skF_9') | ~v1_xboole_0(B_15) | ~v1_xboole_0(u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_32, c_43046])).
% 16.00/8.06  tff(c_43330, plain, (![B_1863]: (r2_hidden(B_1863, '#skF_9') | ~v1_xboole_0(B_1863))), inference(demodulation, [status(thm), theory('equality')], [c_32125, c_43254])).
% 16.00/8.06  tff(c_43428, plain, (![B_1863]: (m1_subset_1(B_1863, '#skF_9') | ~v1_xboole_0(B_1863))), inference(resolution, [status(thm)], [c_43330, c_36])).
% 16.00/8.06  tff(c_33167, plain, (![A_14, B_1502]: (m1_subset_1('#skF_3'(A_14, B_1502), A_14) | B_1502=A_14 | ~m1_subset_1('#skF_2'(A_14, B_1502), A_14) | v1_xboole_0(A_14))), inference(resolution, [status(thm)], [c_30, c_33135])).
% 16.00/8.06  tff(c_43429, plain, (![B_1864]: (m1_subset_1(B_1864, '#skF_9') | ~v1_xboole_0(B_1864))), inference(resolution, [status(thm)], [c_43330, c_36])).
% 16.00/8.06  tff(c_32556, plain, (![A_1449, B_1450]: (~r2_hidden('#skF_2'(A_1449, B_1450), A_1449) | ~r2_hidden('#skF_3'(A_1449, B_1450), B_1450) | B_1450=A_1449)), inference(cnfTransformation, [status(thm)], [f_39])).
% 16.00/8.06  tff(c_35335, plain, (![A_1611, B_1612]: (~r2_hidden('#skF_3'(A_1611, B_1612), B_1612) | B_1612=A_1611 | ~m1_subset_1('#skF_2'(A_1611, B_1612), A_1611) | v1_xboole_0(A_1611))), inference(resolution, [status(thm)], [c_30, c_32556])).
% 16.00/8.06  tff(c_35372, plain, (![A_1611]: (u1_struct_0('#skF_8')=A_1611 | ~m1_subset_1('#skF_2'(A_1611, u1_struct_0('#skF_8')), A_1611) | v1_xboole_0(A_1611) | ~m1_subset_1('#skF_3'(A_1611, u1_struct_0('#skF_8')), '#skF_9'))), inference(resolution, [status(thm)], [c_32552, c_35335])).
% 16.00/8.06  tff(c_43464, plain, (u1_struct_0('#skF_8')='#skF_9' | v1_xboole_0('#skF_9') | ~m1_subset_1('#skF_3'('#skF_9', u1_struct_0('#skF_8')), '#skF_9') | ~v1_xboole_0('#skF_2'('#skF_9', u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_43429, c_35372])).
% 16.00/8.06  tff(c_43517, plain, (u1_struct_0('#skF_8')='#skF_9' | v1_xboole_0('#skF_9') | ~m1_subset_1('#skF_3'('#skF_9', u1_struct_0('#skF_8')), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_40030, c_43464])).
% 16.00/8.06  tff(c_43518, plain, (~m1_subset_1('#skF_3'('#skF_9', u1_struct_0('#skF_8')), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_66, c_38825, c_43517])).
% 16.00/8.06  tff(c_43937, plain, (u1_struct_0('#skF_8')='#skF_9' | ~m1_subset_1('#skF_2'('#skF_9', u1_struct_0('#skF_8')), '#skF_9') | v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_33167, c_43518])).
% 16.00/8.06  tff(c_43957, plain, (~m1_subset_1('#skF_2'('#skF_9', u1_struct_0('#skF_8')), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_66, c_38825, c_43937])).
% 16.00/8.06  tff(c_43989, plain, (~v1_xboole_0('#skF_2'('#skF_9', u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_43428, c_43957])).
% 16.00/8.06  tff(c_44007, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40030, c_43989])).
% 16.00/8.06  tff(c_44009, plain, (r1_tarski(k1_zfmisc_1(u1_struct_0('#skF_8')), k1_zfmisc_1('#skF_9'))), inference(splitRight, [status(thm)], [c_35855])).
% 16.00/8.06  tff(c_32214, plain, (![A_1407, A_1408, C_1409]: (m1_subset_1(A_1407, A_1408) | ~r2_hidden(A_1407, C_1409) | ~r1_tarski(C_1409, A_1408))), inference(resolution, [status(thm)], [c_100, c_16185])).
% 16.00/8.06  tff(c_32235, plain, (![C_13, A_1408, A_9]: (m1_subset_1(C_13, A_1408) | ~r1_tarski(k1_zfmisc_1(A_9), A_1408) | ~r1_tarski(C_13, A_9))), inference(resolution, [status(thm)], [c_18, c_32214])).
% 16.00/8.06  tff(c_35561, plain, (![C_1621, A_1622]: (m1_subset_1(C_1621, k1_zfmisc_1(u1_struct_0('#skF_8'))) | ~r1_tarski(C_1621, A_1622) | ~r1_tarski(k1_zfmisc_1(A_1622), k1_zfmisc_1('#skF_9')))), inference(resolution, [status(thm)], [c_33775, c_32235])).
% 16.00/8.06  tff(c_35598, plain, (![A_1]: (m1_subset_1(A_1, k1_zfmisc_1(u1_struct_0('#skF_8'))) | ~r1_tarski(k1_zfmisc_1(A_1), k1_zfmisc_1('#skF_9')))), inference(resolution, [status(thm)], [c_259, c_35561])).
% 16.00/8.06  tff(c_44086, plain, (m1_subset_1(u1_struct_0('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_44009, c_35598])).
% 16.00/8.06  tff(c_44073, plain, (![B_15]: (r2_hidden(B_15, k1_zfmisc_1('#skF_9')) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0('#skF_8'))) | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_8'))))), inference(resolution, [status(thm)], [c_44009, c_272])).
% 16.00/8.06  tff(c_44329, plain, (![B_1875]: (r2_hidden(B_1875, k1_zfmisc_1('#skF_9')) | ~m1_subset_1(B_1875, k1_zfmisc_1(u1_struct_0('#skF_8'))))), inference(negUnitSimplification, [status(thm)], [c_120, c_44073])).
% 16.00/8.06  tff(c_44414, plain, (r2_hidden(u1_struct_0('#skF_8'), k1_zfmisc_1('#skF_9'))), inference(resolution, [status(thm)], [c_44086, c_44329])).
% 16.00/8.06  tff(c_44508, plain, (r1_tarski(u1_struct_0('#skF_8'), '#skF_9')), inference(resolution, [status(thm)], [c_44414, c_16])).
% 16.00/8.06  tff(c_44520, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35680, c_44508])).
% 16.00/8.06  tff(c_44522, plain, (r1_tarski(u1_struct_0('#skF_8'), '#skF_9')), inference(splitRight, [status(thm)], [c_35678])).
% 16.00/8.06  tff(c_45217, plain, (![A_1898, B_1899, B_1900]: (r2_hidden('#skF_3'(A_1898, B_1899), B_1900) | ~r1_tarski(A_1898, B_1900) | r2_hidden('#skF_2'(A_1898, B_1899), B_1899) | B_1899=A_1898)), inference(resolution, [status(thm)], [c_32126, c_2])).
% 16.00/8.06  tff(c_45334, plain, (![A_1901, B_1902]: (~r1_tarski(A_1901, B_1902) | r2_hidden('#skF_2'(A_1901, B_1902), B_1902) | B_1902=A_1901)), inference(resolution, [status(thm)], [c_45217, c_10])).
% 16.00/8.06  tff(c_45408, plain, (![A_1904, B_1905]: (m1_subset_1('#skF_2'(A_1904, B_1905), B_1905) | ~r1_tarski(A_1904, B_1905) | B_1905=A_1904)), inference(resolution, [status(thm)], [c_45334, c_36])).
% 16.00/8.06  tff(c_35647, plain, (![B_1624]: (~r1_tarski(u1_struct_0('#skF_8'), B_1624) | u1_struct_0('#skF_8')=B_1624 | ~m1_subset_1('#skF_2'(u1_struct_0('#skF_8'), B_1624), '#skF_9'))), inference(resolution, [status(thm)], [c_35599, c_32587])).
% 16.00/8.06  tff(c_45412, plain, (~r1_tarski(u1_struct_0('#skF_8'), '#skF_9') | u1_struct_0('#skF_8')='#skF_9'), inference(resolution, [status(thm)], [c_45408, c_35647])).
% 16.00/8.06  tff(c_45452, plain, (u1_struct_0('#skF_8')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_44522, c_45412])).
% 16.00/8.06  tff(c_45565, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_45452, c_32125])).
% 16.00/8.06  tff(c_45577, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_45565])).
% 16.00/8.06  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.00/8.06  
% 16.00/8.06  Inference rules
% 16.00/8.06  ----------------------
% 16.00/8.06  #Ref     : 0
% 16.00/8.06  #Sup     : 10696
% 16.00/8.06  #Fact    : 0
% 16.00/8.06  #Define  : 0
% 16.00/8.06  #Split   : 126
% 16.00/8.06  #Chain   : 0
% 16.00/8.06  #Close   : 0
% 16.00/8.06  
% 16.00/8.06  Ordering : KBO
% 16.00/8.06  
% 16.00/8.06  Simplification rules
% 16.00/8.06  ----------------------
% 16.00/8.06  #Subsume      : 3089
% 16.00/8.06  #Demod        : 1896
% 16.00/8.06  #Tautology    : 1009
% 16.00/8.06  #SimpNegUnit  : 672
% 16.00/8.06  #BackRed      : 436
% 16.00/8.06  
% 16.00/8.06  #Partial instantiations: 0
% 16.00/8.06  #Strategies tried      : 1
% 16.00/8.06  
% 16.00/8.06  Timing (in seconds)
% 16.00/8.06  ----------------------
% 16.00/8.07  Preprocessing        : 0.32
% 16.00/8.07  Parsing              : 0.17
% 16.00/8.07  CNF conversion       : 0.03
% 16.00/8.07  Main loop            : 6.92
% 16.00/8.07  Inferencing          : 1.56
% 16.00/8.07  Reduction            : 1.72
% 16.00/8.07  Demodulation         : 1.04
% 16.00/8.07  BG Simplification    : 0.16
% 16.00/8.07  Subsumption          : 2.93
% 16.00/8.07  Abstraction          : 0.22
% 16.00/8.07  MUC search           : 0.00
% 16.00/8.07  Cooper               : 0.00
% 16.00/8.07  Total                : 7.33
% 16.00/8.07  Index Insertion      : 0.00
% 16.00/8.07  Index Deletion       : 0.00
% 16.00/8.07  Index Matching       : 0.00
% 16.00/8.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
