%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:04 EST 2020

% Result     : Theorem 5.36s
% Output     : CNFRefutation 5.36s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 294 expanded)
%              Number of leaves         :   38 ( 117 expanded)
%              Depth                    :   14
%              Number of atoms          :  205 (1218 expanded)
%              Number of equality atoms :   22 (  59 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k3_yellow_0 > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

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

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(v1_yellow_0,type,(
    v1_yellow_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_44,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_133,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_104,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(k3_yellow_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_78,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,k3_yellow_0(A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).

tff(f_97,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).

tff(c_10,plain,(
    ! [A_4] : k2_subset_1(A_4) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [A_9] : ~ v1_subset_1(k2_subset_1(A_9),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_69,plain,(
    ! [A_9] : ~ v1_subset_1(A_9,A_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_14])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_169,plain,(
    ! [A_73,B_74] :
      ( r2_hidden('#skF_1'(A_73,B_74),B_74)
      | r2_hidden('#skF_2'(A_73,B_74),A_73)
      | B_74 = A_73 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_571,plain,(
    ! [A_117,B_118,A_119] :
      ( r2_hidden('#skF_2'(A_117,B_118),A_119)
      | ~ m1_subset_1(A_117,k1_zfmisc_1(A_119))
      | r2_hidden('#skF_1'(A_117,B_118),B_118)
      | B_118 = A_117 ) ),
    inference(resolution,[status(thm)],[c_169,c_12])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2),B_2)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_618,plain,(
    ! [A_120,A_121] :
      ( ~ m1_subset_1(A_120,k1_zfmisc_1(A_121))
      | r2_hidden('#skF_1'(A_120,A_121),A_121)
      | A_121 = A_120 ) ),
    inference(resolution,[status(thm)],[c_571,c_4])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,B_11)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_640,plain,(
    ! [A_120,A_121] :
      ( m1_subset_1('#skF_1'(A_120,A_121),A_121)
      | ~ m1_subset_1(A_120,k1_zfmisc_1(A_121))
      | A_121 = A_120 ) ),
    inference(resolution,[status(thm)],[c_618,c_16])).

tff(c_44,plain,(
    v13_waybel_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_84,plain,(
    ! [A_54,B_55] :
      ( r2_hidden(A_54,B_55)
      | v1_xboole_0(B_55)
      | ~ m1_subset_1(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_68,plain,
    ( v1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_82,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_87,plain,
    ( v1_xboole_0('#skF_6')
    | ~ m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_84,c_82])).

tff(c_93,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_87])).

tff(c_50,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_62,plain,
    ( r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
    | ~ v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_83,plain,(
    ~ v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_62])).

tff(c_95,plain,(
    ! [B_56,A_57] :
      ( v1_subset_1(B_56,A_57)
      | B_56 = A_57
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_98,plain,
    ( v1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_42,c_95])).

tff(c_101,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_98])).

tff(c_22,plain,(
    ! [A_17] :
      ( m1_subset_1(k3_yellow_0(A_17),u1_struct_0(A_17))
      | ~ l1_orders_2(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_107,plain,
    ( m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6')
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_22])).

tff(c_111,plain,(
    m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_107])).

tff(c_113,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_111])).

tff(c_115,plain,(
    r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_54,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_52,plain,(
    v1_yellow_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_133,plain,(
    ! [A_62,C_63,B_64] :
      ( m1_subset_1(A_62,C_63)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(C_63))
      | ~ r2_hidden(A_62,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_136,plain,(
    ! [A_62] :
      ( m1_subset_1(A_62,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_62,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_42,c_133])).

tff(c_24,plain,(
    ! [A_18,B_20] :
      ( r1_orders_2(A_18,k3_yellow_0(A_18),B_20)
      | ~ m1_subset_1(B_20,u1_struct_0(A_18))
      | ~ l1_orders_2(A_18)
      | ~ v1_yellow_0(A_18)
      | ~ v5_orders_2(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1398,plain,(
    ! [D_173,B_174,A_175,C_176] :
      ( r2_hidden(D_173,B_174)
      | ~ r1_orders_2(A_175,C_176,D_173)
      | ~ r2_hidden(C_176,B_174)
      | ~ m1_subset_1(D_173,u1_struct_0(A_175))
      | ~ m1_subset_1(C_176,u1_struct_0(A_175))
      | ~ v13_waybel_0(B_174,A_175)
      | ~ m1_subset_1(B_174,k1_zfmisc_1(u1_struct_0(A_175)))
      | ~ l1_orders_2(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2809,plain,(
    ! [B_225,B_226,A_227] :
      ( r2_hidden(B_225,B_226)
      | ~ r2_hidden(k3_yellow_0(A_227),B_226)
      | ~ m1_subset_1(k3_yellow_0(A_227),u1_struct_0(A_227))
      | ~ v13_waybel_0(B_226,A_227)
      | ~ m1_subset_1(B_226,k1_zfmisc_1(u1_struct_0(A_227)))
      | ~ m1_subset_1(B_225,u1_struct_0(A_227))
      | ~ l1_orders_2(A_227)
      | ~ v1_yellow_0(A_227)
      | ~ v5_orders_2(A_227)
      | v2_struct_0(A_227) ) ),
    inference(resolution,[status(thm)],[c_24,c_1398])).

tff(c_2818,plain,(
    ! [B_225,B_226] :
      ( r2_hidden(B_225,B_226)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_226)
      | ~ v13_waybel_0(B_226,'#skF_5')
      | ~ m1_subset_1(B_226,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_225,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v1_yellow_0('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_136,c_2809])).

tff(c_2831,plain,(
    ! [B_225,B_226] :
      ( r2_hidden(B_225,B_226)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_226)
      | ~ v13_waybel_0(B_226,'#skF_5')
      | ~ m1_subset_1(B_226,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_225,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_54,c_52,c_50,c_2818])).

tff(c_3027,plain,(
    ! [B_237,B_238] :
      ( r2_hidden(B_237,B_238)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_238)
      | ~ v13_waybel_0(B_238,'#skF_5')
      | ~ m1_subset_1(B_238,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_237,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2831])).

tff(c_3080,plain,(
    ! [B_237] :
      ( r2_hidden(B_237,'#skF_6')
      | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
      | ~ v13_waybel_0('#skF_6','#skF_5')
      | ~ m1_subset_1(B_237,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_42,c_3027])).

tff(c_3101,plain,(
    ! [B_239] :
      ( r2_hidden(B_239,'#skF_6')
      | ~ m1_subset_1(B_239,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_115,c_3080])).

tff(c_3616,plain,(
    ! [A_252] :
      ( r2_hidden('#skF_1'(A_252,u1_struct_0('#skF_5')),'#skF_6')
      | ~ m1_subset_1(A_252,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | u1_struct_0('#skF_5') = A_252 ) ),
    inference(resolution,[status(thm)],[c_640,c_3101])).

tff(c_196,plain,(
    ! [A_77,B_78] :
      ( ~ r2_hidden('#skF_1'(A_77,B_78),A_77)
      | r2_hidden('#skF_2'(A_77,B_78),A_77)
      | B_78 = A_77 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_209,plain,(
    ! [A_77,B_78] :
      ( m1_subset_1('#skF_2'(A_77,B_78),A_77)
      | ~ r2_hidden('#skF_1'(A_77,B_78),A_77)
      | B_78 = A_77 ) ),
    inference(resolution,[status(thm)],[c_196,c_16])).

tff(c_3623,plain,
    ( m1_subset_1('#skF_2'('#skF_6',u1_struct_0('#skF_5')),'#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_3616,c_209])).

tff(c_3637,plain,
    ( m1_subset_1('#skF_2'('#skF_6',u1_struct_0('#skF_5')),'#skF_6')
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_3623])).

tff(c_3643,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_3637])).

tff(c_114,plain,(
    v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_3662,plain,(
    v1_subset_1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3643,c_114])).

tff(c_3665,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_3662])).

tff(c_3666,plain,(
    m1_subset_1('#skF_2'('#skF_6',u1_struct_0('#skF_5')),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_3637])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( r2_hidden(A_12,B_13)
      | v1_xboole_0(B_13)
      | ~ m1_subset_1(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_138,plain,(
    ! [C_66,A_67,B_68] :
      ( r2_hidden(C_66,A_67)
      | ~ r2_hidden(C_66,B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_210,plain,(
    ! [A_79,A_80,B_81] :
      ( r2_hidden(A_79,A_80)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_80))
      | v1_xboole_0(B_81)
      | ~ m1_subset_1(A_79,B_81) ) ),
    inference(resolution,[status(thm)],[c_18,c_138])).

tff(c_215,plain,(
    ! [A_79] :
      ( r2_hidden(A_79,u1_struct_0('#skF_5'))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_79,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_42,c_210])).

tff(c_219,plain,(
    ! [A_79] :
      ( r2_hidden(A_79,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_79,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_215])).

tff(c_3667,plain,(
    u1_struct_0('#skF_5') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_3637])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),A_1)
      | ~ r2_hidden('#skF_2'(A_1,B_2),B_2)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3626,plain,
    ( ~ r2_hidden('#skF_2'('#skF_6',u1_struct_0('#skF_5')),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_3616,c_2])).

tff(c_3640,plain,
    ( ~ r2_hidden('#skF_2'('#skF_6',u1_struct_0('#skF_5')),u1_struct_0('#skF_5'))
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_3626])).

tff(c_3716,plain,(
    ~ r2_hidden('#skF_2'('#skF_6',u1_struct_0('#skF_5')),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_3667,c_3640])).

tff(c_3725,plain,(
    ~ m1_subset_1('#skF_2'('#skF_6',u1_struct_0('#skF_5')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_219,c_3716])).

tff(c_3740,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3666,c_3725])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:39:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.36/2.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.36/2.05  
% 5.36/2.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.36/2.06  %$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k3_yellow_0 > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 5.36/2.06  
% 5.36/2.06  %Foreground sorts:
% 5.36/2.06  
% 5.36/2.06  
% 5.36/2.06  %Background operators:
% 5.36/2.06  
% 5.36/2.06  
% 5.36/2.06  %Foreground operators:
% 5.36/2.06  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.36/2.06  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 5.36/2.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.36/2.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.36/2.06  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 5.36/2.06  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 5.36/2.06  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 5.36/2.06  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 5.36/2.06  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.36/2.06  tff('#skF_5', type, '#skF_5': $i).
% 5.36/2.06  tff('#skF_6', type, '#skF_6': $i).
% 5.36/2.06  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 5.36/2.06  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 5.36/2.06  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.36/2.06  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 5.36/2.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.36/2.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.36/2.06  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.36/2.06  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 5.36/2.06  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.36/2.06  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.36/2.06  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.36/2.06  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.36/2.06  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.36/2.06  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 5.36/2.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.36/2.06  
% 5.36/2.07  tff(f_34, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 5.36/2.07  tff(f_44, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 5.36/2.07  tff(f_133, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_subset_1(B, u1_struct_0(A)) <=> ~r2_hidden(k3_yellow_0(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_7)).
% 5.36/2.07  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 5.36/2.07  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 5.36/2.07  tff(f_48, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 5.36/2.07  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 5.36/2.07  tff(f_104, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 5.36/2.07  tff(f_64, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(k3_yellow_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow_0)).
% 5.36/2.07  tff(f_60, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 5.36/2.07  tff(f_78, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, k3_yellow_0(A), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_yellow_0)).
% 5.36/2.07  tff(f_97, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v13_waybel_0(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r1_orders_2(A, C, D)) => r2_hidden(D, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_waybel_0)).
% 5.36/2.07  tff(c_10, plain, (![A_4]: (k2_subset_1(A_4)=A_4)), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.36/2.07  tff(c_14, plain, (![A_9]: (~v1_subset_1(k2_subset_1(A_9), A_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.36/2.07  tff(c_69, plain, (![A_9]: (~v1_subset_1(A_9, A_9))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_14])).
% 5.36/2.07  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.36/2.07  tff(c_169, plain, (![A_73, B_74]: (r2_hidden('#skF_1'(A_73, B_74), B_74) | r2_hidden('#skF_2'(A_73, B_74), A_73) | B_74=A_73)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.36/2.07  tff(c_12, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.36/2.07  tff(c_571, plain, (![A_117, B_118, A_119]: (r2_hidden('#skF_2'(A_117, B_118), A_119) | ~m1_subset_1(A_117, k1_zfmisc_1(A_119)) | r2_hidden('#skF_1'(A_117, B_118), B_118) | B_118=A_117)), inference(resolution, [status(thm)], [c_169, c_12])).
% 5.36/2.07  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | ~r2_hidden('#skF_2'(A_1, B_2), B_2) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.36/2.07  tff(c_618, plain, (![A_120, A_121]: (~m1_subset_1(A_120, k1_zfmisc_1(A_121)) | r2_hidden('#skF_1'(A_120, A_121), A_121) | A_121=A_120)), inference(resolution, [status(thm)], [c_571, c_4])).
% 5.36/2.07  tff(c_16, plain, (![A_10, B_11]: (m1_subset_1(A_10, B_11) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.36/2.07  tff(c_640, plain, (![A_120, A_121]: (m1_subset_1('#skF_1'(A_120, A_121), A_121) | ~m1_subset_1(A_120, k1_zfmisc_1(A_121)) | A_121=A_120)), inference(resolution, [status(thm)], [c_618, c_16])).
% 5.36/2.07  tff(c_44, plain, (v13_waybel_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.36/2.07  tff(c_48, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.36/2.07  tff(c_84, plain, (![A_54, B_55]: (r2_hidden(A_54, B_55) | v1_xboole_0(B_55) | ~m1_subset_1(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.36/2.07  tff(c_68, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.36/2.07  tff(c_82, plain, (~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_68])).
% 5.36/2.07  tff(c_87, plain, (v1_xboole_0('#skF_6') | ~m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_84, c_82])).
% 5.36/2.07  tff(c_93, plain, (~m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_48, c_87])).
% 5.36/2.07  tff(c_50, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.36/2.07  tff(c_62, plain, (r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.36/2.07  tff(c_83, plain, (~v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_82, c_62])).
% 5.36/2.07  tff(c_95, plain, (![B_56, A_57]: (v1_subset_1(B_56, A_57) | B_56=A_57 | ~m1_subset_1(B_56, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.36/2.07  tff(c_98, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5')) | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_42, c_95])).
% 5.36/2.07  tff(c_101, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_83, c_98])).
% 5.36/2.07  tff(c_22, plain, (![A_17]: (m1_subset_1(k3_yellow_0(A_17), u1_struct_0(A_17)) | ~l1_orders_2(A_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.36/2.07  tff(c_107, plain, (m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6') | ~l1_orders_2('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_101, c_22])).
% 5.36/2.07  tff(c_111, plain, (m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_107])).
% 5.36/2.07  tff(c_113, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93, c_111])).
% 5.36/2.07  tff(c_115, plain, (r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_68])).
% 5.36/2.07  tff(c_60, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.36/2.07  tff(c_54, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.36/2.07  tff(c_52, plain, (v1_yellow_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.36/2.07  tff(c_133, plain, (![A_62, C_63, B_64]: (m1_subset_1(A_62, C_63) | ~m1_subset_1(B_64, k1_zfmisc_1(C_63)) | ~r2_hidden(A_62, B_64))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.36/2.07  tff(c_136, plain, (![A_62]: (m1_subset_1(A_62, u1_struct_0('#skF_5')) | ~r2_hidden(A_62, '#skF_6'))), inference(resolution, [status(thm)], [c_42, c_133])).
% 5.36/2.07  tff(c_24, plain, (![A_18, B_20]: (r1_orders_2(A_18, k3_yellow_0(A_18), B_20) | ~m1_subset_1(B_20, u1_struct_0(A_18)) | ~l1_orders_2(A_18) | ~v1_yellow_0(A_18) | ~v5_orders_2(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.36/2.07  tff(c_1398, plain, (![D_173, B_174, A_175, C_176]: (r2_hidden(D_173, B_174) | ~r1_orders_2(A_175, C_176, D_173) | ~r2_hidden(C_176, B_174) | ~m1_subset_1(D_173, u1_struct_0(A_175)) | ~m1_subset_1(C_176, u1_struct_0(A_175)) | ~v13_waybel_0(B_174, A_175) | ~m1_subset_1(B_174, k1_zfmisc_1(u1_struct_0(A_175))) | ~l1_orders_2(A_175))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.36/2.07  tff(c_2809, plain, (![B_225, B_226, A_227]: (r2_hidden(B_225, B_226) | ~r2_hidden(k3_yellow_0(A_227), B_226) | ~m1_subset_1(k3_yellow_0(A_227), u1_struct_0(A_227)) | ~v13_waybel_0(B_226, A_227) | ~m1_subset_1(B_226, k1_zfmisc_1(u1_struct_0(A_227))) | ~m1_subset_1(B_225, u1_struct_0(A_227)) | ~l1_orders_2(A_227) | ~v1_yellow_0(A_227) | ~v5_orders_2(A_227) | v2_struct_0(A_227))), inference(resolution, [status(thm)], [c_24, c_1398])).
% 5.36/2.07  tff(c_2818, plain, (![B_225, B_226]: (r2_hidden(B_225, B_226) | ~r2_hidden(k3_yellow_0('#skF_5'), B_226) | ~v13_waybel_0(B_226, '#skF_5') | ~m1_subset_1(B_226, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_225, u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v1_yellow_0('#skF_5') | ~v5_orders_2('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_136, c_2809])).
% 5.36/2.07  tff(c_2831, plain, (![B_225, B_226]: (r2_hidden(B_225, B_226) | ~r2_hidden(k3_yellow_0('#skF_5'), B_226) | ~v13_waybel_0(B_226, '#skF_5') | ~m1_subset_1(B_226, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_225, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_54, c_52, c_50, c_2818])).
% 5.36/2.07  tff(c_3027, plain, (![B_237, B_238]: (r2_hidden(B_237, B_238) | ~r2_hidden(k3_yellow_0('#skF_5'), B_238) | ~v13_waybel_0(B_238, '#skF_5') | ~m1_subset_1(B_238, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_237, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_60, c_2831])).
% 5.36/2.07  tff(c_3080, plain, (![B_237]: (r2_hidden(B_237, '#skF_6') | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v13_waybel_0('#skF_6', '#skF_5') | ~m1_subset_1(B_237, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_42, c_3027])).
% 5.36/2.07  tff(c_3101, plain, (![B_239]: (r2_hidden(B_239, '#skF_6') | ~m1_subset_1(B_239, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_115, c_3080])).
% 5.36/2.07  tff(c_3616, plain, (![A_252]: (r2_hidden('#skF_1'(A_252, u1_struct_0('#skF_5')), '#skF_6') | ~m1_subset_1(A_252, k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')=A_252)), inference(resolution, [status(thm)], [c_640, c_3101])).
% 5.36/2.07  tff(c_196, plain, (![A_77, B_78]: (~r2_hidden('#skF_1'(A_77, B_78), A_77) | r2_hidden('#skF_2'(A_77, B_78), A_77) | B_78=A_77)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.36/2.07  tff(c_209, plain, (![A_77, B_78]: (m1_subset_1('#skF_2'(A_77, B_78), A_77) | ~r2_hidden('#skF_1'(A_77, B_78), A_77) | B_78=A_77)), inference(resolution, [status(thm)], [c_196, c_16])).
% 5.36/2.07  tff(c_3623, plain, (m1_subset_1('#skF_2'('#skF_6', u1_struct_0('#skF_5')), '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_3616, c_209])).
% 5.36/2.07  tff(c_3637, plain, (m1_subset_1('#skF_2'('#skF_6', u1_struct_0('#skF_5')), '#skF_6') | u1_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_3623])).
% 5.36/2.07  tff(c_3643, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(splitLeft, [status(thm)], [c_3637])).
% 5.36/2.07  tff(c_114, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_68])).
% 5.36/2.07  tff(c_3662, plain, (v1_subset_1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3643, c_114])).
% 5.36/2.07  tff(c_3665, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_3662])).
% 5.36/2.07  tff(c_3666, plain, (m1_subset_1('#skF_2'('#skF_6', u1_struct_0('#skF_5')), '#skF_6')), inference(splitRight, [status(thm)], [c_3637])).
% 5.36/2.07  tff(c_18, plain, (![A_12, B_13]: (r2_hidden(A_12, B_13) | v1_xboole_0(B_13) | ~m1_subset_1(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.36/2.07  tff(c_138, plain, (![C_66, A_67, B_68]: (r2_hidden(C_66, A_67) | ~r2_hidden(C_66, B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.36/2.07  tff(c_210, plain, (![A_79, A_80, B_81]: (r2_hidden(A_79, A_80) | ~m1_subset_1(B_81, k1_zfmisc_1(A_80)) | v1_xboole_0(B_81) | ~m1_subset_1(A_79, B_81))), inference(resolution, [status(thm)], [c_18, c_138])).
% 5.36/2.07  tff(c_215, plain, (![A_79]: (r2_hidden(A_79, u1_struct_0('#skF_5')) | v1_xboole_0('#skF_6') | ~m1_subset_1(A_79, '#skF_6'))), inference(resolution, [status(thm)], [c_42, c_210])).
% 5.36/2.07  tff(c_219, plain, (![A_79]: (r2_hidden(A_79, u1_struct_0('#skF_5')) | ~m1_subset_1(A_79, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_48, c_215])).
% 5.36/2.07  tff(c_3667, plain, (u1_struct_0('#skF_5')!='#skF_6'), inference(splitRight, [status(thm)], [c_3637])).
% 5.36/2.07  tff(c_2, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), A_1) | ~r2_hidden('#skF_2'(A_1, B_2), B_2) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.36/2.07  tff(c_3626, plain, (~r2_hidden('#skF_2'('#skF_6', u1_struct_0('#skF_5')), u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_3616, c_2])).
% 5.36/2.07  tff(c_3640, plain, (~r2_hidden('#skF_2'('#skF_6', u1_struct_0('#skF_5')), u1_struct_0('#skF_5')) | u1_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_3626])).
% 5.36/2.07  tff(c_3716, plain, (~r2_hidden('#skF_2'('#skF_6', u1_struct_0('#skF_5')), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_3667, c_3640])).
% 5.36/2.07  tff(c_3725, plain, (~m1_subset_1('#skF_2'('#skF_6', u1_struct_0('#skF_5')), '#skF_6')), inference(resolution, [status(thm)], [c_219, c_3716])).
% 5.36/2.07  tff(c_3740, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3666, c_3725])).
% 5.36/2.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.36/2.07  
% 5.36/2.07  Inference rules
% 5.36/2.07  ----------------------
% 5.36/2.07  #Ref     : 0
% 5.36/2.07  #Sup     : 744
% 5.36/2.07  #Fact    : 0
% 5.36/2.07  #Define  : 0
% 5.36/2.07  #Split   : 10
% 5.36/2.07  #Chain   : 0
% 5.36/2.07  #Close   : 0
% 5.36/2.07  
% 5.36/2.07  Ordering : KBO
% 5.36/2.07  
% 5.36/2.07  Simplification rules
% 5.36/2.07  ----------------------
% 5.36/2.07  #Subsume      : 95
% 5.36/2.07  #Demod        : 199
% 5.36/2.07  #Tautology    : 118
% 5.36/2.07  #SimpNegUnit  : 37
% 5.36/2.07  #BackRed      : 60
% 5.36/2.07  
% 5.36/2.07  #Partial instantiations: 0
% 5.36/2.07  #Strategies tried      : 1
% 5.36/2.07  
% 5.36/2.07  Timing (in seconds)
% 5.36/2.07  ----------------------
% 5.36/2.08  Preprocessing        : 0.32
% 5.36/2.08  Parsing              : 0.18
% 5.36/2.08  CNF conversion       : 0.03
% 5.36/2.08  Main loop            : 0.96
% 5.36/2.08  Inferencing          : 0.30
% 5.36/2.08  Reduction            : 0.24
% 5.36/2.08  Demodulation         : 0.15
% 5.36/2.08  BG Simplification    : 0.04
% 5.36/2.08  Subsumption          : 0.31
% 5.36/2.08  Abstraction          : 0.04
% 5.36/2.08  MUC search           : 0.00
% 5.36/2.08  Cooper               : 0.00
% 5.36/2.08  Total                : 1.31
% 5.36/2.08  Index Insertion      : 0.00
% 5.36/2.08  Index Deletion       : 0.00
% 5.36/2.08  Index Matching       : 0.00
% 5.76/2.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
