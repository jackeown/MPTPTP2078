%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:04 EST 2020

% Result     : Theorem 5.91s
% Output     : CNFRefutation 5.91s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 464 expanded)
%              Number of leaves         :   38 ( 173 expanded)
%              Depth                    :   13
%              Number of atoms          :  243 (1764 expanded)
%              Number of equality atoms :   31 ( 131 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_132,negated_conjecture,(
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
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(k3_yellow_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_77,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,k3_yellow_0(A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_yellow_0)).

tff(f_96,axiom,(
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

tff(c_10,plain,(
    ! [A_4] : k2_subset_1(A_4) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_12,plain,(
    ! [A_5] : m1_subset_1(k2_subset_1(A_5),k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_69,plain,(
    ! [A_5] : m1_subset_1(A_5,k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_40,plain,(
    ! [B_47] :
      ( ~ v1_subset_1(B_47,B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_71,plain,(
    ! [B_47] : ~ v1_subset_1(B_47,B_47) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_40])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_184,plain,(
    ! [A_72,B_73] :
      ( r2_hidden('#skF_1'(A_72,B_73),B_73)
      | r2_hidden('#skF_2'(A_72,B_73),A_72)
      | B_73 = A_72 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,B_11)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_231,plain,(
    ! [A_80,B_81] :
      ( m1_subset_1('#skF_2'(A_80,B_81),A_80)
      | r2_hidden('#skF_1'(A_80,B_81),B_81)
      | B_81 = A_80 ) ),
    inference(resolution,[status(thm)],[c_184,c_16])).

tff(c_14,plain,(
    ! [C_9,A_6,B_7] :
      ( r2_hidden(C_9,A_6)
      | ~ r2_hidden(C_9,B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_959,plain,(
    ! [A_148,B_149,A_150] :
      ( r2_hidden('#skF_1'(A_148,B_149),A_150)
      | ~ m1_subset_1(B_149,k1_zfmisc_1(A_150))
      | m1_subset_1('#skF_2'(A_148,B_149),A_148)
      | B_149 = A_148 ) ),
    inference(resolution,[status(thm)],[c_231,c_14])).

tff(c_217,plain,(
    ! [A_78,B_79] :
      ( ~ r2_hidden('#skF_1'(A_78,B_79),A_78)
      | r2_hidden('#skF_2'(A_78,B_79),A_78)
      | B_79 = A_78 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_230,plain,(
    ! [A_78,B_79] :
      ( m1_subset_1('#skF_2'(A_78,B_79),A_78)
      | ~ r2_hidden('#skF_1'(A_78,B_79),A_78)
      | B_79 = A_78 ) ),
    inference(resolution,[status(thm)],[c_217,c_16])).

tff(c_1000,plain,(
    ! [B_149,A_150] :
      ( ~ m1_subset_1(B_149,k1_zfmisc_1(A_150))
      | m1_subset_1('#skF_2'(A_150,B_149),A_150)
      | B_149 = A_150 ) ),
    inference(resolution,[status(thm)],[c_959,c_230])).

tff(c_44,plain,(
    v13_waybel_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_87,plain,(
    ! [A_55,B_56] :
      ( r2_hidden(A_55,B_56)
      | v1_xboole_0(B_56)
      | ~ m1_subset_1(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_62,plain,
    ( r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
    | ~ v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_85,plain,(
    ~ v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_68,plain,
    ( v1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_86,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_68])).

tff(c_90,plain,
    ( v1_xboole_0('#skF_6')
    | ~ m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_87,c_86])).

tff(c_96,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_90])).

tff(c_50,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_98,plain,(
    ! [B_57,A_58] :
      ( v1_subset_1(B_57,A_58)
      | B_57 = A_58
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_101,plain,
    ( v1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_42,c_98])).

tff(c_107,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_101])).

tff(c_22,plain,(
    ! [A_17] :
      ( m1_subset_1(k3_yellow_0(A_17),u1_struct_0(A_17))
      | ~ l1_orders_2(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_118,plain,
    ( m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6')
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_22])).

tff(c_122,plain,(
    m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_118])).

tff(c_124,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_122])).

tff(c_125,plain,(
    r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_54,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_52,plain,(
    v1_yellow_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_172,plain,(
    ! [A_68,C_69,B_70] :
      ( m1_subset_1(A_68,C_69)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(C_69))
      | ~ r2_hidden(A_68,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_181,plain,(
    ! [A_68] :
      ( m1_subset_1(A_68,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_68,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_42,c_172])).

tff(c_24,plain,(
    ! [A_18,B_20] :
      ( r1_orders_2(A_18,k3_yellow_0(A_18),B_20)
      | ~ m1_subset_1(B_20,u1_struct_0(A_18))
      | ~ l1_orders_2(A_18)
      | ~ v1_yellow_0(A_18)
      | ~ v5_orders_2(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1301,plain,(
    ! [D_170,B_171,A_172,C_173] :
      ( r2_hidden(D_170,B_171)
      | ~ r1_orders_2(A_172,C_173,D_170)
      | ~ r2_hidden(C_173,B_171)
      | ~ m1_subset_1(D_170,u1_struct_0(A_172))
      | ~ m1_subset_1(C_173,u1_struct_0(A_172))
      | ~ v13_waybel_0(B_171,A_172)
      | ~ m1_subset_1(B_171,k1_zfmisc_1(u1_struct_0(A_172)))
      | ~ l1_orders_2(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2629,plain,(
    ! [B_219,B_220,A_221] :
      ( r2_hidden(B_219,B_220)
      | ~ r2_hidden(k3_yellow_0(A_221),B_220)
      | ~ m1_subset_1(k3_yellow_0(A_221),u1_struct_0(A_221))
      | ~ v13_waybel_0(B_220,A_221)
      | ~ m1_subset_1(B_220,k1_zfmisc_1(u1_struct_0(A_221)))
      | ~ m1_subset_1(B_219,u1_struct_0(A_221))
      | ~ l1_orders_2(A_221)
      | ~ v1_yellow_0(A_221)
      | ~ v5_orders_2(A_221)
      | v2_struct_0(A_221) ) ),
    inference(resolution,[status(thm)],[c_24,c_1301])).

tff(c_2637,plain,(
    ! [B_219,B_220] :
      ( r2_hidden(B_219,B_220)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_220)
      | ~ v13_waybel_0(B_220,'#skF_5')
      | ~ m1_subset_1(B_220,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_219,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v1_yellow_0('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_181,c_2629])).

tff(c_2653,plain,(
    ! [B_219,B_220] :
      ( r2_hidden(B_219,B_220)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_220)
      | ~ v13_waybel_0(B_220,'#skF_5')
      | ~ m1_subset_1(B_220,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_219,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_54,c_52,c_50,c_2637])).

tff(c_2794,plain,(
    ! [B_229,B_230] :
      ( r2_hidden(B_229,B_230)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_230)
      | ~ v13_waybel_0(B_230,'#skF_5')
      | ~ m1_subset_1(B_230,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_229,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2653])).

tff(c_2850,plain,(
    ! [B_229] :
      ( r2_hidden(B_229,'#skF_6')
      | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
      | ~ v13_waybel_0('#skF_6','#skF_5')
      | ~ m1_subset_1(B_229,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_42,c_2794])).

tff(c_2878,plain,(
    ! [B_231] :
      ( r2_hidden(B_231,'#skF_6')
      | ~ m1_subset_1(B_231,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_125,c_2850])).

tff(c_3567,plain,(
    ! [B_250] :
      ( r2_hidden('#skF_2'(u1_struct_0('#skF_5'),B_250),'#skF_6')
      | ~ m1_subset_1(B_250,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | u1_struct_0('#skF_5') = B_250 ) ),
    inference(resolution,[status(thm)],[c_1000,c_2878])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( r2_hidden(A_12,B_13)
      | v1_xboole_0(B_13)
      | ~ m1_subset_1(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_151,plain,(
    ! [C_63,A_64,B_65] :
      ( r2_hidden(C_63,A_64)
      | ~ r2_hidden(C_63,B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_252,plain,(
    ! [A_82,A_83,B_84] :
      ( r2_hidden(A_82,A_83)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_83))
      | v1_xboole_0(B_84)
      | ~ m1_subset_1(A_82,B_84) ) ),
    inference(resolution,[status(thm)],[c_18,c_151])).

tff(c_260,plain,(
    ! [A_82] :
      ( r2_hidden(A_82,u1_struct_0('#skF_5'))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_82,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_42,c_252])).

tff(c_269,plain,(
    ! [A_85] :
      ( r2_hidden(A_85,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_85,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_260])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),A_1)
      | ~ r2_hidden('#skF_2'(A_1,B_2),B_2)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_283,plain,(
    ! [B_2] :
      ( ~ r2_hidden('#skF_2'(u1_struct_0('#skF_5'),B_2),B_2)
      | u1_struct_0('#skF_5') = B_2
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),B_2),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_269,c_2])).

tff(c_3578,plain,
    ( ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),'#skF_6'),'#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_3567,c_283])).

tff(c_3597,plain,
    ( ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),'#skF_6'),'#skF_6')
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_3578])).

tff(c_3603,plain,(
    ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),'#skF_6'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_3597])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2),B_2)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3582,plain,
    ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),'#skF_6'),'#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_3567,c_4])).

tff(c_3600,plain,
    ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),'#skF_6'),'#skF_6')
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_3582])).

tff(c_3620,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_3600])).

tff(c_267,plain,(
    ! [A_82] :
      ( r2_hidden(A_82,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_82,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_260])).

tff(c_636,plain,(
    ! [A_122,B_123,A_124] :
      ( r2_hidden('#skF_2'(A_122,B_123),A_124)
      | ~ m1_subset_1(A_122,k1_zfmisc_1(A_124))
      | r2_hidden('#skF_1'(A_122,B_123),B_123)
      | B_123 = A_122 ) ),
    inference(resolution,[status(thm)],[c_184,c_14])).

tff(c_683,plain,(
    ! [A_125,A_126] :
      ( ~ m1_subset_1(A_125,k1_zfmisc_1(A_126))
      | r2_hidden('#skF_1'(A_125,A_126),A_126)
      | A_126 = A_125 ) ),
    inference(resolution,[status(thm)],[c_636,c_4])).

tff(c_732,plain,(
    ! [A_129,A_130,A_131] :
      ( r2_hidden('#skF_1'(A_129,A_130),A_131)
      | ~ m1_subset_1(A_130,k1_zfmisc_1(A_131))
      | ~ m1_subset_1(A_129,k1_zfmisc_1(A_130))
      | A_130 = A_129 ) ),
    inference(resolution,[status(thm)],[c_683,c_14])).

tff(c_806,plain,(
    ! [A_139,A_140] :
      ( ~ r2_hidden('#skF_2'(A_139,A_140),A_140)
      | ~ m1_subset_1(A_140,k1_zfmisc_1(A_139))
      | ~ m1_subset_1(A_139,k1_zfmisc_1(A_140))
      | A_140 = A_139 ) ),
    inference(resolution,[status(thm)],[c_732,c_2])).

tff(c_2575,plain,(
    ! [A_217] :
      ( ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_217))
      | ~ m1_subset_1(A_217,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | u1_struct_0('#skF_5') = A_217
      | ~ m1_subset_1('#skF_2'(A_217,u1_struct_0('#skF_5')),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_267,c_806])).

tff(c_2587,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1('#skF_6'))
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1000,c_2575])).

tff(c_2603,plain,
    ( ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1('#skF_6'))
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2587])).

tff(c_2613,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_2603])).

tff(c_3631,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3620,c_2613])).

tff(c_3654,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_3631])).

tff(c_3655,plain,(
    r2_hidden('#skF_1'(u1_struct_0('#skF_5'),'#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_3600])).

tff(c_3661,plain,(
    m1_subset_1('#skF_1'(u1_struct_0('#skF_5'),'#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_3655,c_16])).

tff(c_3666,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3603,c_3661])).

tff(c_3667,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_3597])).

tff(c_3678,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3667,c_2613])).

tff(c_3701,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_3678])).

tff(c_3702,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2603])).

tff(c_126,plain,(
    v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_3752,plain,(
    v1_subset_1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3702,c_126])).

tff(c_3757,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_3752])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:38:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.91/2.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.91/2.17  
% 5.91/2.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.91/2.17  %$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k3_yellow_0 > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 5.91/2.17  
% 5.91/2.17  %Foreground sorts:
% 5.91/2.17  
% 5.91/2.17  
% 5.91/2.17  %Background operators:
% 5.91/2.17  
% 5.91/2.17  
% 5.91/2.17  %Foreground operators:
% 5.91/2.17  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.91/2.17  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 5.91/2.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.91/2.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.91/2.17  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 5.91/2.17  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 5.91/2.17  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 5.91/2.17  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 5.91/2.17  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.91/2.17  tff('#skF_5', type, '#skF_5': $i).
% 5.91/2.17  tff('#skF_6', type, '#skF_6': $i).
% 5.91/2.17  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 5.91/2.17  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 5.91/2.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.91/2.17  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 5.91/2.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.91/2.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.91/2.17  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.91/2.17  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 5.91/2.17  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.91/2.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.91/2.17  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.91/2.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.91/2.17  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.91/2.17  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 5.91/2.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.91/2.17  
% 5.91/2.19  tff(f_34, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 5.91/2.19  tff(f_36, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 5.91/2.19  tff(f_103, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 5.91/2.19  tff(f_132, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_subset_1(B, u1_struct_0(A)) <=> ~r2_hidden(k3_yellow_0(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_7)).
% 5.91/2.19  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 5.91/2.19  tff(f_47, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 5.91/2.19  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 5.91/2.19  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 5.91/2.19  tff(f_63, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(k3_yellow_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow_0)).
% 5.91/2.19  tff(f_59, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 5.91/2.19  tff(f_77, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, k3_yellow_0(A), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_yellow_0)).
% 5.91/2.19  tff(f_96, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v13_waybel_0(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r1_orders_2(A, C, D)) => r2_hidden(D, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_waybel_0)).
% 5.91/2.19  tff(c_10, plain, (![A_4]: (k2_subset_1(A_4)=A_4)), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.91/2.19  tff(c_12, plain, (![A_5]: (m1_subset_1(k2_subset_1(A_5), k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.91/2.19  tff(c_69, plain, (![A_5]: (m1_subset_1(A_5, k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 5.91/2.19  tff(c_40, plain, (![B_47]: (~v1_subset_1(B_47, B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(B_47)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.91/2.19  tff(c_71, plain, (![B_47]: (~v1_subset_1(B_47, B_47))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_40])).
% 5.91/2.19  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.91/2.19  tff(c_184, plain, (![A_72, B_73]: (r2_hidden('#skF_1'(A_72, B_73), B_73) | r2_hidden('#skF_2'(A_72, B_73), A_72) | B_73=A_72)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.91/2.19  tff(c_16, plain, (![A_10, B_11]: (m1_subset_1(A_10, B_11) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.91/2.19  tff(c_231, plain, (![A_80, B_81]: (m1_subset_1('#skF_2'(A_80, B_81), A_80) | r2_hidden('#skF_1'(A_80, B_81), B_81) | B_81=A_80)), inference(resolution, [status(thm)], [c_184, c_16])).
% 5.91/2.19  tff(c_14, plain, (![C_9, A_6, B_7]: (r2_hidden(C_9, A_6) | ~r2_hidden(C_9, B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.91/2.19  tff(c_959, plain, (![A_148, B_149, A_150]: (r2_hidden('#skF_1'(A_148, B_149), A_150) | ~m1_subset_1(B_149, k1_zfmisc_1(A_150)) | m1_subset_1('#skF_2'(A_148, B_149), A_148) | B_149=A_148)), inference(resolution, [status(thm)], [c_231, c_14])).
% 5.91/2.19  tff(c_217, plain, (![A_78, B_79]: (~r2_hidden('#skF_1'(A_78, B_79), A_78) | r2_hidden('#skF_2'(A_78, B_79), A_78) | B_79=A_78)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.91/2.19  tff(c_230, plain, (![A_78, B_79]: (m1_subset_1('#skF_2'(A_78, B_79), A_78) | ~r2_hidden('#skF_1'(A_78, B_79), A_78) | B_79=A_78)), inference(resolution, [status(thm)], [c_217, c_16])).
% 5.91/2.19  tff(c_1000, plain, (![B_149, A_150]: (~m1_subset_1(B_149, k1_zfmisc_1(A_150)) | m1_subset_1('#skF_2'(A_150, B_149), A_150) | B_149=A_150)), inference(resolution, [status(thm)], [c_959, c_230])).
% 5.91/2.19  tff(c_44, plain, (v13_waybel_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.91/2.19  tff(c_48, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.91/2.19  tff(c_87, plain, (![A_55, B_56]: (r2_hidden(A_55, B_56) | v1_xboole_0(B_56) | ~m1_subset_1(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.91/2.19  tff(c_62, plain, (r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.91/2.19  tff(c_85, plain, (~v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_62])).
% 5.91/2.19  tff(c_68, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.91/2.19  tff(c_86, plain, (~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_85, c_68])).
% 5.91/2.19  tff(c_90, plain, (v1_xboole_0('#skF_6') | ~m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_87, c_86])).
% 5.91/2.19  tff(c_96, plain, (~m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_48, c_90])).
% 5.91/2.19  tff(c_50, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.91/2.19  tff(c_98, plain, (![B_57, A_58]: (v1_subset_1(B_57, A_58) | B_57=A_58 | ~m1_subset_1(B_57, k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.91/2.19  tff(c_101, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5')) | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_42, c_98])).
% 5.91/2.19  tff(c_107, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_85, c_101])).
% 5.91/2.19  tff(c_22, plain, (![A_17]: (m1_subset_1(k3_yellow_0(A_17), u1_struct_0(A_17)) | ~l1_orders_2(A_17))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.91/2.19  tff(c_118, plain, (m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6') | ~l1_orders_2('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_107, c_22])).
% 5.91/2.19  tff(c_122, plain, (m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_118])).
% 5.91/2.19  tff(c_124, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_122])).
% 5.91/2.19  tff(c_125, plain, (r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_62])).
% 5.91/2.19  tff(c_60, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.91/2.19  tff(c_54, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.91/2.19  tff(c_52, plain, (v1_yellow_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.91/2.19  tff(c_172, plain, (![A_68, C_69, B_70]: (m1_subset_1(A_68, C_69) | ~m1_subset_1(B_70, k1_zfmisc_1(C_69)) | ~r2_hidden(A_68, B_70))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.91/2.19  tff(c_181, plain, (![A_68]: (m1_subset_1(A_68, u1_struct_0('#skF_5')) | ~r2_hidden(A_68, '#skF_6'))), inference(resolution, [status(thm)], [c_42, c_172])).
% 5.91/2.19  tff(c_24, plain, (![A_18, B_20]: (r1_orders_2(A_18, k3_yellow_0(A_18), B_20) | ~m1_subset_1(B_20, u1_struct_0(A_18)) | ~l1_orders_2(A_18) | ~v1_yellow_0(A_18) | ~v5_orders_2(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.91/2.19  tff(c_1301, plain, (![D_170, B_171, A_172, C_173]: (r2_hidden(D_170, B_171) | ~r1_orders_2(A_172, C_173, D_170) | ~r2_hidden(C_173, B_171) | ~m1_subset_1(D_170, u1_struct_0(A_172)) | ~m1_subset_1(C_173, u1_struct_0(A_172)) | ~v13_waybel_0(B_171, A_172) | ~m1_subset_1(B_171, k1_zfmisc_1(u1_struct_0(A_172))) | ~l1_orders_2(A_172))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.91/2.19  tff(c_2629, plain, (![B_219, B_220, A_221]: (r2_hidden(B_219, B_220) | ~r2_hidden(k3_yellow_0(A_221), B_220) | ~m1_subset_1(k3_yellow_0(A_221), u1_struct_0(A_221)) | ~v13_waybel_0(B_220, A_221) | ~m1_subset_1(B_220, k1_zfmisc_1(u1_struct_0(A_221))) | ~m1_subset_1(B_219, u1_struct_0(A_221)) | ~l1_orders_2(A_221) | ~v1_yellow_0(A_221) | ~v5_orders_2(A_221) | v2_struct_0(A_221))), inference(resolution, [status(thm)], [c_24, c_1301])).
% 5.91/2.19  tff(c_2637, plain, (![B_219, B_220]: (r2_hidden(B_219, B_220) | ~r2_hidden(k3_yellow_0('#skF_5'), B_220) | ~v13_waybel_0(B_220, '#skF_5') | ~m1_subset_1(B_220, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_219, u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v1_yellow_0('#skF_5') | ~v5_orders_2('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_181, c_2629])).
% 5.91/2.19  tff(c_2653, plain, (![B_219, B_220]: (r2_hidden(B_219, B_220) | ~r2_hidden(k3_yellow_0('#skF_5'), B_220) | ~v13_waybel_0(B_220, '#skF_5') | ~m1_subset_1(B_220, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_219, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_54, c_52, c_50, c_2637])).
% 5.91/2.19  tff(c_2794, plain, (![B_229, B_230]: (r2_hidden(B_229, B_230) | ~r2_hidden(k3_yellow_0('#skF_5'), B_230) | ~v13_waybel_0(B_230, '#skF_5') | ~m1_subset_1(B_230, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_229, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_60, c_2653])).
% 5.91/2.19  tff(c_2850, plain, (![B_229]: (r2_hidden(B_229, '#skF_6') | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v13_waybel_0('#skF_6', '#skF_5') | ~m1_subset_1(B_229, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_42, c_2794])).
% 5.91/2.19  tff(c_2878, plain, (![B_231]: (r2_hidden(B_231, '#skF_6') | ~m1_subset_1(B_231, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_125, c_2850])).
% 5.91/2.19  tff(c_3567, plain, (![B_250]: (r2_hidden('#skF_2'(u1_struct_0('#skF_5'), B_250), '#skF_6') | ~m1_subset_1(B_250, k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')=B_250)), inference(resolution, [status(thm)], [c_1000, c_2878])).
% 5.91/2.19  tff(c_18, plain, (![A_12, B_13]: (r2_hidden(A_12, B_13) | v1_xboole_0(B_13) | ~m1_subset_1(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.91/2.19  tff(c_151, plain, (![C_63, A_64, B_65]: (r2_hidden(C_63, A_64) | ~r2_hidden(C_63, B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.91/2.19  tff(c_252, plain, (![A_82, A_83, B_84]: (r2_hidden(A_82, A_83) | ~m1_subset_1(B_84, k1_zfmisc_1(A_83)) | v1_xboole_0(B_84) | ~m1_subset_1(A_82, B_84))), inference(resolution, [status(thm)], [c_18, c_151])).
% 5.91/2.19  tff(c_260, plain, (![A_82]: (r2_hidden(A_82, u1_struct_0('#skF_5')) | v1_xboole_0('#skF_6') | ~m1_subset_1(A_82, '#skF_6'))), inference(resolution, [status(thm)], [c_42, c_252])).
% 5.91/2.19  tff(c_269, plain, (![A_85]: (r2_hidden(A_85, u1_struct_0('#skF_5')) | ~m1_subset_1(A_85, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_48, c_260])).
% 5.91/2.19  tff(c_2, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), A_1) | ~r2_hidden('#skF_2'(A_1, B_2), B_2) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.91/2.19  tff(c_283, plain, (![B_2]: (~r2_hidden('#skF_2'(u1_struct_0('#skF_5'), B_2), B_2) | u1_struct_0('#skF_5')=B_2 | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), B_2), '#skF_6'))), inference(resolution, [status(thm)], [c_269, c_2])).
% 5.91/2.19  tff(c_3578, plain, (~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), '#skF_6'), '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_3567, c_283])).
% 5.91/2.19  tff(c_3597, plain, (~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), '#skF_6'), '#skF_6') | u1_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_3578])).
% 5.91/2.19  tff(c_3603, plain, (~m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), '#skF_6'), '#skF_6')), inference(splitLeft, [status(thm)], [c_3597])).
% 5.91/2.19  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | ~r2_hidden('#skF_2'(A_1, B_2), B_2) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.91/2.19  tff(c_3582, plain, (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), '#skF_6'), '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_3567, c_4])).
% 5.91/2.19  tff(c_3600, plain, (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), '#skF_6'), '#skF_6') | u1_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_3582])).
% 5.91/2.19  tff(c_3620, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(splitLeft, [status(thm)], [c_3600])).
% 5.91/2.19  tff(c_267, plain, (![A_82]: (r2_hidden(A_82, u1_struct_0('#skF_5')) | ~m1_subset_1(A_82, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_48, c_260])).
% 5.91/2.19  tff(c_636, plain, (![A_122, B_123, A_124]: (r2_hidden('#skF_2'(A_122, B_123), A_124) | ~m1_subset_1(A_122, k1_zfmisc_1(A_124)) | r2_hidden('#skF_1'(A_122, B_123), B_123) | B_123=A_122)), inference(resolution, [status(thm)], [c_184, c_14])).
% 5.91/2.19  tff(c_683, plain, (![A_125, A_126]: (~m1_subset_1(A_125, k1_zfmisc_1(A_126)) | r2_hidden('#skF_1'(A_125, A_126), A_126) | A_126=A_125)), inference(resolution, [status(thm)], [c_636, c_4])).
% 5.91/2.19  tff(c_732, plain, (![A_129, A_130, A_131]: (r2_hidden('#skF_1'(A_129, A_130), A_131) | ~m1_subset_1(A_130, k1_zfmisc_1(A_131)) | ~m1_subset_1(A_129, k1_zfmisc_1(A_130)) | A_130=A_129)), inference(resolution, [status(thm)], [c_683, c_14])).
% 5.91/2.19  tff(c_806, plain, (![A_139, A_140]: (~r2_hidden('#skF_2'(A_139, A_140), A_140) | ~m1_subset_1(A_140, k1_zfmisc_1(A_139)) | ~m1_subset_1(A_139, k1_zfmisc_1(A_140)) | A_140=A_139)), inference(resolution, [status(thm)], [c_732, c_2])).
% 5.91/2.19  tff(c_2575, plain, (![A_217]: (~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_217)) | ~m1_subset_1(A_217, k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')=A_217 | ~m1_subset_1('#skF_2'(A_217, u1_struct_0('#skF_5')), '#skF_6'))), inference(resolution, [status(thm)], [c_267, c_806])).
% 5.91/2.19  tff(c_2587, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1('#skF_6')) | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_1000, c_2575])).
% 5.91/2.19  tff(c_2603, plain, (~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1('#skF_6')) | u1_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2587])).
% 5.91/2.19  tff(c_2613, plain, (~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_2603])).
% 5.91/2.19  tff(c_3631, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_3620, c_2613])).
% 5.91/2.19  tff(c_3654, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69, c_3631])).
% 5.91/2.19  tff(c_3655, plain, (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), '#skF_6'), '#skF_6')), inference(splitRight, [status(thm)], [c_3600])).
% 5.91/2.19  tff(c_3661, plain, (m1_subset_1('#skF_1'(u1_struct_0('#skF_5'), '#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_3655, c_16])).
% 5.91/2.19  tff(c_3666, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3603, c_3661])).
% 5.91/2.19  tff(c_3667, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_3597])).
% 5.91/2.19  tff(c_3678, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_3667, c_2613])).
% 5.91/2.19  tff(c_3701, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69, c_3678])).
% 5.91/2.19  tff(c_3702, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_2603])).
% 5.91/2.19  tff(c_126, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_62])).
% 5.91/2.19  tff(c_3752, plain, (v1_subset_1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3702, c_126])).
% 5.91/2.19  tff(c_3757, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_3752])).
% 5.91/2.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.91/2.19  
% 5.91/2.19  Inference rules
% 5.91/2.19  ----------------------
% 5.91/2.19  #Ref     : 0
% 5.91/2.19  #Sup     : 704
% 5.91/2.19  #Fact    : 0
% 5.91/2.19  #Define  : 0
% 5.91/2.19  #Split   : 12
% 5.91/2.19  #Chain   : 0
% 5.91/2.19  #Close   : 0
% 5.91/2.19  
% 5.91/2.19  Ordering : KBO
% 5.91/2.19  
% 5.91/2.19  Simplification rules
% 5.91/2.19  ----------------------
% 5.91/2.19  #Subsume      : 95
% 5.91/2.19  #Demod        : 359
% 5.91/2.19  #Tautology    : 140
% 5.91/2.19  #SimpNegUnit  : 47
% 5.91/2.19  #BackRed      : 102
% 5.91/2.19  
% 5.91/2.19  #Partial instantiations: 0
% 5.91/2.19  #Strategies tried      : 1
% 5.91/2.19  
% 5.91/2.19  Timing (in seconds)
% 5.91/2.19  ----------------------
% 5.91/2.19  Preprocessing        : 0.37
% 5.91/2.19  Parsing              : 0.19
% 5.91/2.19  CNF conversion       : 0.03
% 5.91/2.19  Main loop            : 1.03
% 5.91/2.19  Inferencing          : 0.33
% 5.91/2.19  Reduction            : 0.29
% 5.91/2.19  Demodulation         : 0.19
% 5.91/2.19  BG Simplification    : 0.04
% 5.91/2.19  Subsumption          : 0.29
% 5.91/2.19  Abstraction          : 0.05
% 5.91/2.19  MUC search           : 0.00
% 5.91/2.19  Cooper               : 0.00
% 5.91/2.19  Total                : 1.44
% 5.91/2.19  Index Insertion      : 0.00
% 5.91/2.19  Index Deletion       : 0.00
% 5.91/2.19  Index Matching       : 0.00
% 5.91/2.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
