%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:04 EST 2020

% Result     : Theorem 5.86s
% Output     : CNFRefutation 5.92s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 403 expanded)
%              Number of leaves         :   37 ( 153 expanded)
%              Depth                    :   14
%              Number of atoms          :  241 (1563 expanded)
%              Number of equality atoms :   32 ( 108 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > #skF_7 > #skF_6 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

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

tff(f_45,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_134,negated_conjecture,(
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

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(k3_yellow_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_79,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,k3_yellow_0(A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_yellow_0)).

tff(f_98,axiom,(
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

tff(c_12,plain,(
    ! [A_8] : ~ v1_subset_1('#skF_3'(A_8),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14,plain,(
    ! [A_8] : m1_subset_1('#skF_3'(A_8),k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_137,plain,(
    ! [B_63,A_64] :
      ( v1_subset_1(B_63,A_64)
      | B_63 = A_64
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_140,plain,(
    ! [A_8] :
      ( v1_subset_1('#skF_3'(A_8),A_8)
      | '#skF_3'(A_8) = A_8 ) ),
    inference(resolution,[status(thm)],[c_14,c_137])).

tff(c_146,plain,(
    ! [A_8] : '#skF_3'(A_8) = A_8 ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_140])).

tff(c_150,plain,(
    ! [A_8] : ~ v1_subset_1(A_8,A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_12])).

tff(c_149,plain,(
    ! [A_8] : m1_subset_1(A_8,k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_14])).

tff(c_42,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_202,plain,(
    ! [A_77,B_78] :
      ( r2_hidden('#skF_1'(A_77,B_78),B_78)
      | r2_hidden('#skF_2'(A_77,B_78),A_77)
      | B_78 = A_77 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [C_7,A_4,B_5] :
      ( r2_hidden(C_7,A_4)
      | ~ r2_hidden(C_7,B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_637,plain,(
    ! [A_128,B_129,A_130] :
      ( r2_hidden('#skF_2'(A_128,B_129),A_130)
      | ~ m1_subset_1(A_128,k1_zfmisc_1(A_130))
      | r2_hidden('#skF_1'(A_128,B_129),B_129)
      | B_129 = A_128 ) ),
    inference(resolution,[status(thm)],[c_202,c_10])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2),B_2)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_684,plain,(
    ! [A_131,A_132] :
      ( ~ m1_subset_1(A_131,k1_zfmisc_1(A_132))
      | r2_hidden('#skF_1'(A_131,A_132),A_132)
      | A_132 = A_131 ) ),
    inference(resolution,[status(thm)],[c_637,c_4])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,B_11)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_710,plain,(
    ! [A_131,A_132] :
      ( m1_subset_1('#skF_1'(A_131,A_132),A_132)
      | ~ m1_subset_1(A_131,k1_zfmisc_1(A_132))
      | A_132 = A_131 ) ),
    inference(resolution,[status(thm)],[c_684,c_16])).

tff(c_44,plain,(
    v13_waybel_0('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( r2_hidden(A_12,B_13)
      | v1_xboole_0(B_13)
      | ~ m1_subset_1(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_62,plain,
    ( r2_hidden(k3_yellow_0('#skF_6'),'#skF_7')
    | ~ v1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_74,plain,(
    ~ v1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_68,plain,
    ( v1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ r2_hidden(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_80,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68])).

tff(c_83,plain,
    ( v1_xboole_0('#skF_7')
    | ~ m1_subset_1(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_18,c_80])).

tff(c_86,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_83])).

tff(c_50,plain,(
    l1_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_87,plain,(
    ! [B_57,A_58] :
      ( v1_subset_1(B_57,A_58)
      | B_57 = A_58
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_93,plain,
    ( v1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | u1_struct_0('#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_42,c_87])).

tff(c_99,plain,(
    u1_struct_0('#skF_6') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_93])).

tff(c_22,plain,(
    ! [A_17] :
      ( m1_subset_1(k3_yellow_0(A_17),u1_struct_0(A_17))
      | ~ l1_orders_2(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_117,plain,
    ( m1_subset_1(k3_yellow_0('#skF_6'),'#skF_7')
    | ~ l1_orders_2('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_22])).

tff(c_121,plain,(
    m1_subset_1(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_117])).

tff(c_123,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_121])).

tff(c_124,plain,(
    r2_hidden(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_54,plain,(
    v5_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_52,plain,(
    v1_yellow_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_169,plain,(
    ! [A_68,C_69,B_70] :
      ( m1_subset_1(A_68,C_69)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(C_69))
      | ~ r2_hidden(A_68,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_175,plain,(
    ! [A_68] :
      ( m1_subset_1(A_68,u1_struct_0('#skF_6'))
      | ~ r2_hidden(A_68,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_42,c_169])).

tff(c_24,plain,(
    ! [A_18,B_20] :
      ( r1_orders_2(A_18,k3_yellow_0(A_18),B_20)
      | ~ m1_subset_1(B_20,u1_struct_0(A_18))
      | ~ l1_orders_2(A_18)
      | ~ v1_yellow_0(A_18)
      | ~ v5_orders_2(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1192,plain,(
    ! [D_168,B_169,A_170,C_171] :
      ( r2_hidden(D_168,B_169)
      | ~ r1_orders_2(A_170,C_171,D_168)
      | ~ r2_hidden(C_171,B_169)
      | ~ m1_subset_1(D_168,u1_struct_0(A_170))
      | ~ m1_subset_1(C_171,u1_struct_0(A_170))
      | ~ v13_waybel_0(B_169,A_170)
      | ~ m1_subset_1(B_169,k1_zfmisc_1(u1_struct_0(A_170)))
      | ~ l1_orders_2(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2920,plain,(
    ! [B_229,B_230,A_231] :
      ( r2_hidden(B_229,B_230)
      | ~ r2_hidden(k3_yellow_0(A_231),B_230)
      | ~ m1_subset_1(k3_yellow_0(A_231),u1_struct_0(A_231))
      | ~ v13_waybel_0(B_230,A_231)
      | ~ m1_subset_1(B_230,k1_zfmisc_1(u1_struct_0(A_231)))
      | ~ m1_subset_1(B_229,u1_struct_0(A_231))
      | ~ l1_orders_2(A_231)
      | ~ v1_yellow_0(A_231)
      | ~ v5_orders_2(A_231)
      | v2_struct_0(A_231) ) ),
    inference(resolution,[status(thm)],[c_24,c_1192])).

tff(c_2931,plain,(
    ! [B_229,B_230] :
      ( r2_hidden(B_229,B_230)
      | ~ r2_hidden(k3_yellow_0('#skF_6'),B_230)
      | ~ v13_waybel_0(B_230,'#skF_6')
      | ~ m1_subset_1(B_230,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(B_229,u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | ~ v1_yellow_0('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ r2_hidden(k3_yellow_0('#skF_6'),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_175,c_2920])).

tff(c_2948,plain,(
    ! [B_229,B_230] :
      ( r2_hidden(B_229,B_230)
      | ~ r2_hidden(k3_yellow_0('#skF_6'),B_230)
      | ~ v13_waybel_0(B_230,'#skF_6')
      | ~ m1_subset_1(B_230,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(B_229,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_54,c_52,c_50,c_2931])).

tff(c_3074,plain,(
    ! [B_238,B_239] :
      ( r2_hidden(B_238,B_239)
      | ~ r2_hidden(k3_yellow_0('#skF_6'),B_239)
      | ~ v13_waybel_0(B_239,'#skF_6')
      | ~ m1_subset_1(B_239,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(B_238,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2948])).

tff(c_3130,plain,(
    ! [B_238] :
      ( r2_hidden(B_238,'#skF_7')
      | ~ r2_hidden(k3_yellow_0('#skF_6'),'#skF_7')
      | ~ v13_waybel_0('#skF_7','#skF_6')
      | ~ m1_subset_1(B_238,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_42,c_3074])).

tff(c_3154,plain,(
    ! [B_240] :
      ( r2_hidden(B_240,'#skF_7')
      | ~ m1_subset_1(B_240,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_124,c_3130])).

tff(c_3817,plain,(
    ! [A_259] :
      ( r2_hidden('#skF_1'(A_259,u1_struct_0('#skF_6')),'#skF_7')
      | ~ m1_subset_1(A_259,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | u1_struct_0('#skF_6') = A_259 ) ),
    inference(resolution,[status(thm)],[c_710,c_3154])).

tff(c_244,plain,(
    ! [A_82,B_83] :
      ( ~ r2_hidden('#skF_1'(A_82,B_83),A_82)
      | r2_hidden('#skF_2'(A_82,B_83),A_82)
      | B_83 = A_82 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_251,plain,(
    ! [A_82,B_83] :
      ( m1_subset_1('#skF_2'(A_82,B_83),A_82)
      | ~ r2_hidden('#skF_1'(A_82,B_83),A_82)
      | B_83 = A_82 ) ),
    inference(resolution,[status(thm)],[c_244,c_16])).

tff(c_3824,plain,
    ( m1_subset_1('#skF_2'('#skF_7',u1_struct_0('#skF_6')),'#skF_7')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6')))
    | u1_struct_0('#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_3817,c_251])).

tff(c_3838,plain,
    ( m1_subset_1('#skF_2'('#skF_7',u1_struct_0('#skF_6')),'#skF_7')
    | u1_struct_0('#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_3824])).

tff(c_3844,plain,(
    u1_struct_0('#skF_6') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_3838])).

tff(c_904,plain,(
    ! [A_151,B_152,A_153] :
      ( r2_hidden('#skF_1'(A_151,B_152),A_153)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(A_153))
      | r2_hidden('#skF_2'(A_151,B_152),A_151)
      | B_152 = A_151 ) ),
    inference(resolution,[status(thm)],[c_202,c_10])).

tff(c_1060,plain,(
    ! [A_160,B_161,A_162] :
      ( m1_subset_1('#skF_2'(A_160,B_161),A_160)
      | r2_hidden('#skF_1'(A_160,B_161),A_162)
      | ~ m1_subset_1(B_161,k1_zfmisc_1(A_162))
      | B_161 = A_160 ) ),
    inference(resolution,[status(thm)],[c_904,c_16])).

tff(c_1108,plain,(
    ! [A_162,B_161] :
      ( m1_subset_1('#skF_2'(A_162,B_161),A_162)
      | ~ m1_subset_1(B_161,k1_zfmisc_1(A_162))
      | B_161 = A_162 ) ),
    inference(resolution,[status(thm)],[c_1060,c_251])).

tff(c_177,plain,(
    ! [C_72,A_73,B_74] :
      ( r2_hidden(C_72,A_73)
      | ~ r2_hidden(C_72,B_74)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_328,plain,(
    ! [A_92,A_93,B_94] :
      ( r2_hidden(A_92,A_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_93))
      | v1_xboole_0(B_94)
      | ~ m1_subset_1(A_92,B_94) ) ),
    inference(resolution,[status(thm)],[c_18,c_177])).

tff(c_341,plain,(
    ! [A_92] :
      ( r2_hidden(A_92,u1_struct_0('#skF_6'))
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(A_92,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_42,c_328])).

tff(c_348,plain,(
    ! [A_92] :
      ( r2_hidden(A_92,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(A_92,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_341])).

tff(c_751,plain,(
    ! [A_136,A_137,A_138] :
      ( r2_hidden('#skF_1'(A_136,A_137),A_138)
      | ~ m1_subset_1(A_137,k1_zfmisc_1(A_138))
      | ~ m1_subset_1(A_136,k1_zfmisc_1(A_137))
      | A_137 = A_136 ) ),
    inference(resolution,[status(thm)],[c_684,c_10])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),A_1)
      | ~ r2_hidden('#skF_2'(A_1,B_2),B_2)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_802,plain,(
    ! [A_141,A_142] :
      ( ~ r2_hidden('#skF_2'(A_141,A_142),A_142)
      | ~ m1_subset_1(A_142,k1_zfmisc_1(A_141))
      | ~ m1_subset_1(A_141,k1_zfmisc_1(A_142))
      | A_142 = A_141 ) ),
    inference(resolution,[status(thm)],[c_751,c_2])).

tff(c_2881,plain,(
    ! [A_228] :
      ( ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(A_228))
      | ~ m1_subset_1(A_228,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | u1_struct_0('#skF_6') = A_228
      | ~ m1_subset_1('#skF_2'(A_228,u1_struct_0('#skF_6')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_348,c_802])).

tff(c_2893,plain,
    ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1('#skF_7'))
    | u1_struct_0('#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1108,c_2881])).

tff(c_2909,plain,
    ( ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1('#skF_7'))
    | u1_struct_0('#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2893])).

tff(c_2919,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_2909])).

tff(c_3854,plain,(
    ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3844,c_2919])).

tff(c_3877,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_3854])).

tff(c_3878,plain,(
    m1_subset_1('#skF_2'('#skF_7',u1_struct_0('#skF_6')),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_3838])).

tff(c_3879,plain,(
    u1_struct_0('#skF_6') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_3838])).

tff(c_3827,plain,
    ( ~ r2_hidden('#skF_2'('#skF_7',u1_struct_0('#skF_6')),u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6')))
    | u1_struct_0('#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_3817,c_2])).

tff(c_3841,plain,
    ( ~ r2_hidden('#skF_2'('#skF_7',u1_struct_0('#skF_6')),u1_struct_0('#skF_6'))
    | u1_struct_0('#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_3827])).

tff(c_3887,plain,(
    ~ r2_hidden('#skF_2'('#skF_7',u1_struct_0('#skF_6')),u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_3879,c_3841])).

tff(c_3899,plain,(
    ~ m1_subset_1('#skF_2'('#skF_7',u1_struct_0('#skF_6')),'#skF_7') ),
    inference(resolution,[status(thm)],[c_348,c_3887])).

tff(c_3915,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3878,c_3899])).

tff(c_3916,plain,(
    u1_struct_0('#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_2909])).

tff(c_125,plain,(
    v1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_3935,plain,(
    v1_subset_1('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3916,c_125])).

tff(c_3940,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_3935])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:08:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.86/2.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.92/2.07  
% 5.92/2.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.92/2.07  %$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > #skF_7 > #skF_6 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 5.92/2.07  
% 5.92/2.07  %Foreground sorts:
% 5.92/2.07  
% 5.92/2.07  
% 5.92/2.07  %Background operators:
% 5.92/2.07  
% 5.92/2.07  
% 5.92/2.07  %Foreground operators:
% 5.92/2.07  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.92/2.07  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 5.92/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.92/2.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.92/2.07  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 5.92/2.07  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 5.92/2.07  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 5.92/2.07  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 5.92/2.07  tff('#skF_7', type, '#skF_7': $i).
% 5.92/2.07  tff('#skF_6', type, '#skF_6': $i).
% 5.92/2.07  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 5.92/2.07  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 5.92/2.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.92/2.07  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 5.92/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.92/2.07  tff('#skF_3', type, '#skF_3': $i > $i).
% 5.92/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.92/2.07  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.92/2.07  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 5.92/2.07  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.92/2.07  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.92/2.07  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.92/2.07  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.92/2.07  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.92/2.07  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 5.92/2.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.92/2.07  
% 5.92/2.09  tff(f_45, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_subset_1)).
% 5.92/2.09  tff(f_105, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 5.92/2.09  tff(f_134, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_subset_1(B, u1_struct_0(A)) <=> ~r2_hidden(k3_yellow_0(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_7)).
% 5.92/2.09  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 5.92/2.09  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 5.92/2.09  tff(f_49, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 5.92/2.09  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 5.92/2.09  tff(f_65, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(k3_yellow_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow_0)).
% 5.92/2.09  tff(f_61, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 5.92/2.09  tff(f_79, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, k3_yellow_0(A), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_yellow_0)).
% 5.92/2.09  tff(f_98, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v13_waybel_0(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r1_orders_2(A, C, D)) => r2_hidden(D, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_waybel_0)).
% 5.92/2.09  tff(c_12, plain, (![A_8]: (~v1_subset_1('#skF_3'(A_8), A_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.92/2.09  tff(c_14, plain, (![A_8]: (m1_subset_1('#skF_3'(A_8), k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.92/2.09  tff(c_137, plain, (![B_63, A_64]: (v1_subset_1(B_63, A_64) | B_63=A_64 | ~m1_subset_1(B_63, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.92/2.09  tff(c_140, plain, (![A_8]: (v1_subset_1('#skF_3'(A_8), A_8) | '#skF_3'(A_8)=A_8)), inference(resolution, [status(thm)], [c_14, c_137])).
% 5.92/2.09  tff(c_146, plain, (![A_8]: ('#skF_3'(A_8)=A_8)), inference(negUnitSimplification, [status(thm)], [c_12, c_140])).
% 5.92/2.09  tff(c_150, plain, (![A_8]: (~v1_subset_1(A_8, A_8))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_12])).
% 5.92/2.09  tff(c_149, plain, (![A_8]: (m1_subset_1(A_8, k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_14])).
% 5.92/2.09  tff(c_42, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.92/2.09  tff(c_202, plain, (![A_77, B_78]: (r2_hidden('#skF_1'(A_77, B_78), B_78) | r2_hidden('#skF_2'(A_77, B_78), A_77) | B_78=A_77)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.92/2.09  tff(c_10, plain, (![C_7, A_4, B_5]: (r2_hidden(C_7, A_4) | ~r2_hidden(C_7, B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.92/2.09  tff(c_637, plain, (![A_128, B_129, A_130]: (r2_hidden('#skF_2'(A_128, B_129), A_130) | ~m1_subset_1(A_128, k1_zfmisc_1(A_130)) | r2_hidden('#skF_1'(A_128, B_129), B_129) | B_129=A_128)), inference(resolution, [status(thm)], [c_202, c_10])).
% 5.92/2.09  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | ~r2_hidden('#skF_2'(A_1, B_2), B_2) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.92/2.09  tff(c_684, plain, (![A_131, A_132]: (~m1_subset_1(A_131, k1_zfmisc_1(A_132)) | r2_hidden('#skF_1'(A_131, A_132), A_132) | A_132=A_131)), inference(resolution, [status(thm)], [c_637, c_4])).
% 5.92/2.09  tff(c_16, plain, (![A_10, B_11]: (m1_subset_1(A_10, B_11) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.92/2.09  tff(c_710, plain, (![A_131, A_132]: (m1_subset_1('#skF_1'(A_131, A_132), A_132) | ~m1_subset_1(A_131, k1_zfmisc_1(A_132)) | A_132=A_131)), inference(resolution, [status(thm)], [c_684, c_16])).
% 5.92/2.09  tff(c_44, plain, (v13_waybel_0('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.92/2.09  tff(c_48, plain, (~v1_xboole_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.92/2.09  tff(c_18, plain, (![A_12, B_13]: (r2_hidden(A_12, B_13) | v1_xboole_0(B_13) | ~m1_subset_1(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.92/2.09  tff(c_62, plain, (r2_hidden(k3_yellow_0('#skF_6'), '#skF_7') | ~v1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.92/2.09  tff(c_74, plain, (~v1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_62])).
% 5.92/2.09  tff(c_68, plain, (v1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~r2_hidden(k3_yellow_0('#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.92/2.09  tff(c_80, plain, (~r2_hidden(k3_yellow_0('#skF_6'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_74, c_68])).
% 5.92/2.09  tff(c_83, plain, (v1_xboole_0('#skF_7') | ~m1_subset_1(k3_yellow_0('#skF_6'), '#skF_7')), inference(resolution, [status(thm)], [c_18, c_80])).
% 5.92/2.09  tff(c_86, plain, (~m1_subset_1(k3_yellow_0('#skF_6'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_48, c_83])).
% 5.92/2.09  tff(c_50, plain, (l1_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.92/2.09  tff(c_87, plain, (![B_57, A_58]: (v1_subset_1(B_57, A_58) | B_57=A_58 | ~m1_subset_1(B_57, k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.92/2.09  tff(c_93, plain, (v1_subset_1('#skF_7', u1_struct_0('#skF_6')) | u1_struct_0('#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_42, c_87])).
% 5.92/2.09  tff(c_99, plain, (u1_struct_0('#skF_6')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_74, c_93])).
% 5.92/2.09  tff(c_22, plain, (![A_17]: (m1_subset_1(k3_yellow_0(A_17), u1_struct_0(A_17)) | ~l1_orders_2(A_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.92/2.09  tff(c_117, plain, (m1_subset_1(k3_yellow_0('#skF_6'), '#skF_7') | ~l1_orders_2('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_99, c_22])).
% 5.92/2.09  tff(c_121, plain, (m1_subset_1(k3_yellow_0('#skF_6'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_117])).
% 5.92/2.09  tff(c_123, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_121])).
% 5.92/2.09  tff(c_124, plain, (r2_hidden(k3_yellow_0('#skF_6'), '#skF_7')), inference(splitRight, [status(thm)], [c_62])).
% 5.92/2.09  tff(c_60, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.92/2.09  tff(c_54, plain, (v5_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.92/2.09  tff(c_52, plain, (v1_yellow_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.92/2.09  tff(c_169, plain, (![A_68, C_69, B_70]: (m1_subset_1(A_68, C_69) | ~m1_subset_1(B_70, k1_zfmisc_1(C_69)) | ~r2_hidden(A_68, B_70))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.92/2.09  tff(c_175, plain, (![A_68]: (m1_subset_1(A_68, u1_struct_0('#skF_6')) | ~r2_hidden(A_68, '#skF_7'))), inference(resolution, [status(thm)], [c_42, c_169])).
% 5.92/2.09  tff(c_24, plain, (![A_18, B_20]: (r1_orders_2(A_18, k3_yellow_0(A_18), B_20) | ~m1_subset_1(B_20, u1_struct_0(A_18)) | ~l1_orders_2(A_18) | ~v1_yellow_0(A_18) | ~v5_orders_2(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.92/2.09  tff(c_1192, plain, (![D_168, B_169, A_170, C_171]: (r2_hidden(D_168, B_169) | ~r1_orders_2(A_170, C_171, D_168) | ~r2_hidden(C_171, B_169) | ~m1_subset_1(D_168, u1_struct_0(A_170)) | ~m1_subset_1(C_171, u1_struct_0(A_170)) | ~v13_waybel_0(B_169, A_170) | ~m1_subset_1(B_169, k1_zfmisc_1(u1_struct_0(A_170))) | ~l1_orders_2(A_170))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.92/2.09  tff(c_2920, plain, (![B_229, B_230, A_231]: (r2_hidden(B_229, B_230) | ~r2_hidden(k3_yellow_0(A_231), B_230) | ~m1_subset_1(k3_yellow_0(A_231), u1_struct_0(A_231)) | ~v13_waybel_0(B_230, A_231) | ~m1_subset_1(B_230, k1_zfmisc_1(u1_struct_0(A_231))) | ~m1_subset_1(B_229, u1_struct_0(A_231)) | ~l1_orders_2(A_231) | ~v1_yellow_0(A_231) | ~v5_orders_2(A_231) | v2_struct_0(A_231))), inference(resolution, [status(thm)], [c_24, c_1192])).
% 5.92/2.09  tff(c_2931, plain, (![B_229, B_230]: (r2_hidden(B_229, B_230) | ~r2_hidden(k3_yellow_0('#skF_6'), B_230) | ~v13_waybel_0(B_230, '#skF_6') | ~m1_subset_1(B_230, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1(B_229, u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v1_yellow_0('#skF_6') | ~v5_orders_2('#skF_6') | v2_struct_0('#skF_6') | ~r2_hidden(k3_yellow_0('#skF_6'), '#skF_7'))), inference(resolution, [status(thm)], [c_175, c_2920])).
% 5.92/2.09  tff(c_2948, plain, (![B_229, B_230]: (r2_hidden(B_229, B_230) | ~r2_hidden(k3_yellow_0('#skF_6'), B_230) | ~v13_waybel_0(B_230, '#skF_6') | ~m1_subset_1(B_230, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1(B_229, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_54, c_52, c_50, c_2931])).
% 5.92/2.09  tff(c_3074, plain, (![B_238, B_239]: (r2_hidden(B_238, B_239) | ~r2_hidden(k3_yellow_0('#skF_6'), B_239) | ~v13_waybel_0(B_239, '#skF_6') | ~m1_subset_1(B_239, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1(B_238, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_60, c_2948])).
% 5.92/2.09  tff(c_3130, plain, (![B_238]: (r2_hidden(B_238, '#skF_7') | ~r2_hidden(k3_yellow_0('#skF_6'), '#skF_7') | ~v13_waybel_0('#skF_7', '#skF_6') | ~m1_subset_1(B_238, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_42, c_3074])).
% 5.92/2.09  tff(c_3154, plain, (![B_240]: (r2_hidden(B_240, '#skF_7') | ~m1_subset_1(B_240, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_124, c_3130])).
% 5.92/2.09  tff(c_3817, plain, (![A_259]: (r2_hidden('#skF_1'(A_259, u1_struct_0('#skF_6')), '#skF_7') | ~m1_subset_1(A_259, k1_zfmisc_1(u1_struct_0('#skF_6'))) | u1_struct_0('#skF_6')=A_259)), inference(resolution, [status(thm)], [c_710, c_3154])).
% 5.92/2.09  tff(c_244, plain, (![A_82, B_83]: (~r2_hidden('#skF_1'(A_82, B_83), A_82) | r2_hidden('#skF_2'(A_82, B_83), A_82) | B_83=A_82)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.92/2.09  tff(c_251, plain, (![A_82, B_83]: (m1_subset_1('#skF_2'(A_82, B_83), A_82) | ~r2_hidden('#skF_1'(A_82, B_83), A_82) | B_83=A_82)), inference(resolution, [status(thm)], [c_244, c_16])).
% 5.92/2.09  tff(c_3824, plain, (m1_subset_1('#skF_2'('#skF_7', u1_struct_0('#skF_6')), '#skF_7') | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6'))) | u1_struct_0('#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_3817, c_251])).
% 5.92/2.09  tff(c_3838, plain, (m1_subset_1('#skF_2'('#skF_7', u1_struct_0('#skF_6')), '#skF_7') | u1_struct_0('#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_3824])).
% 5.92/2.09  tff(c_3844, plain, (u1_struct_0('#skF_6')='#skF_7'), inference(splitLeft, [status(thm)], [c_3838])).
% 5.92/2.09  tff(c_904, plain, (![A_151, B_152, A_153]: (r2_hidden('#skF_1'(A_151, B_152), A_153) | ~m1_subset_1(B_152, k1_zfmisc_1(A_153)) | r2_hidden('#skF_2'(A_151, B_152), A_151) | B_152=A_151)), inference(resolution, [status(thm)], [c_202, c_10])).
% 5.92/2.09  tff(c_1060, plain, (![A_160, B_161, A_162]: (m1_subset_1('#skF_2'(A_160, B_161), A_160) | r2_hidden('#skF_1'(A_160, B_161), A_162) | ~m1_subset_1(B_161, k1_zfmisc_1(A_162)) | B_161=A_160)), inference(resolution, [status(thm)], [c_904, c_16])).
% 5.92/2.09  tff(c_1108, plain, (![A_162, B_161]: (m1_subset_1('#skF_2'(A_162, B_161), A_162) | ~m1_subset_1(B_161, k1_zfmisc_1(A_162)) | B_161=A_162)), inference(resolution, [status(thm)], [c_1060, c_251])).
% 5.92/2.09  tff(c_177, plain, (![C_72, A_73, B_74]: (r2_hidden(C_72, A_73) | ~r2_hidden(C_72, B_74) | ~m1_subset_1(B_74, k1_zfmisc_1(A_73)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.92/2.09  tff(c_328, plain, (![A_92, A_93, B_94]: (r2_hidden(A_92, A_93) | ~m1_subset_1(B_94, k1_zfmisc_1(A_93)) | v1_xboole_0(B_94) | ~m1_subset_1(A_92, B_94))), inference(resolution, [status(thm)], [c_18, c_177])).
% 5.92/2.09  tff(c_341, plain, (![A_92]: (r2_hidden(A_92, u1_struct_0('#skF_6')) | v1_xboole_0('#skF_7') | ~m1_subset_1(A_92, '#skF_7'))), inference(resolution, [status(thm)], [c_42, c_328])).
% 5.92/2.09  tff(c_348, plain, (![A_92]: (r2_hidden(A_92, u1_struct_0('#skF_6')) | ~m1_subset_1(A_92, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_48, c_341])).
% 5.92/2.09  tff(c_751, plain, (![A_136, A_137, A_138]: (r2_hidden('#skF_1'(A_136, A_137), A_138) | ~m1_subset_1(A_137, k1_zfmisc_1(A_138)) | ~m1_subset_1(A_136, k1_zfmisc_1(A_137)) | A_137=A_136)), inference(resolution, [status(thm)], [c_684, c_10])).
% 5.92/2.09  tff(c_2, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), A_1) | ~r2_hidden('#skF_2'(A_1, B_2), B_2) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.92/2.09  tff(c_802, plain, (![A_141, A_142]: (~r2_hidden('#skF_2'(A_141, A_142), A_142) | ~m1_subset_1(A_142, k1_zfmisc_1(A_141)) | ~m1_subset_1(A_141, k1_zfmisc_1(A_142)) | A_142=A_141)), inference(resolution, [status(thm)], [c_751, c_2])).
% 5.92/2.09  tff(c_2881, plain, (![A_228]: (~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(A_228)) | ~m1_subset_1(A_228, k1_zfmisc_1(u1_struct_0('#skF_6'))) | u1_struct_0('#skF_6')=A_228 | ~m1_subset_1('#skF_2'(A_228, u1_struct_0('#skF_6')), '#skF_7'))), inference(resolution, [status(thm)], [c_348, c_802])).
% 5.92/2.09  tff(c_2893, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1('#skF_7')) | u1_struct_0('#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_1108, c_2881])).
% 5.92/2.09  tff(c_2909, plain, (~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1('#skF_7')) | u1_struct_0('#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2893])).
% 5.92/2.09  tff(c_2919, plain, (~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_2909])).
% 5.92/2.09  tff(c_3854, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_3844, c_2919])).
% 5.92/2.09  tff(c_3877, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_149, c_3854])).
% 5.92/2.09  tff(c_3878, plain, (m1_subset_1('#skF_2'('#skF_7', u1_struct_0('#skF_6')), '#skF_7')), inference(splitRight, [status(thm)], [c_3838])).
% 5.92/2.09  tff(c_3879, plain, (u1_struct_0('#skF_6')!='#skF_7'), inference(splitRight, [status(thm)], [c_3838])).
% 5.92/2.09  tff(c_3827, plain, (~r2_hidden('#skF_2'('#skF_7', u1_struct_0('#skF_6')), u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6'))) | u1_struct_0('#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_3817, c_2])).
% 5.92/2.09  tff(c_3841, plain, (~r2_hidden('#skF_2'('#skF_7', u1_struct_0('#skF_6')), u1_struct_0('#skF_6')) | u1_struct_0('#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_3827])).
% 5.92/2.09  tff(c_3887, plain, (~r2_hidden('#skF_2'('#skF_7', u1_struct_0('#skF_6')), u1_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_3879, c_3841])).
% 5.92/2.09  tff(c_3899, plain, (~m1_subset_1('#skF_2'('#skF_7', u1_struct_0('#skF_6')), '#skF_7')), inference(resolution, [status(thm)], [c_348, c_3887])).
% 5.92/2.09  tff(c_3915, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3878, c_3899])).
% 5.92/2.09  tff(c_3916, plain, (u1_struct_0('#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_2909])).
% 5.92/2.09  tff(c_125, plain, (v1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_62])).
% 5.92/2.09  tff(c_3935, plain, (v1_subset_1('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3916, c_125])).
% 5.92/2.09  tff(c_3940, plain, $false, inference(negUnitSimplification, [status(thm)], [c_150, c_3935])).
% 5.92/2.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.92/2.09  
% 5.92/2.09  Inference rules
% 5.92/2.09  ----------------------
% 5.92/2.09  #Ref     : 0
% 5.92/2.09  #Sup     : 729
% 5.92/2.09  #Fact    : 0
% 5.92/2.09  #Define  : 0
% 5.92/2.09  #Split   : 13
% 5.92/2.09  #Chain   : 0
% 5.92/2.09  #Close   : 0
% 5.92/2.09  
% 5.92/2.09  Ordering : KBO
% 5.92/2.09  
% 5.92/2.09  Simplification rules
% 5.92/2.09  ----------------------
% 5.92/2.09  #Subsume      : 89
% 5.92/2.09  #Demod        : 393
% 5.92/2.09  #Tautology    : 142
% 5.92/2.09  #SimpNegUnit  : 41
% 5.92/2.09  #BackRed      : 133
% 5.92/2.09  
% 5.92/2.09  #Partial instantiations: 0
% 5.92/2.09  #Strategies tried      : 1
% 5.92/2.09  
% 5.92/2.09  Timing (in seconds)
% 5.92/2.09  ----------------------
% 5.92/2.10  Preprocessing        : 0.32
% 5.92/2.10  Parsing              : 0.18
% 5.92/2.10  CNF conversion       : 0.03
% 5.92/2.10  Main loop            : 1.04
% 5.92/2.10  Inferencing          : 0.33
% 5.92/2.10  Reduction            : 0.28
% 5.92/2.10  Demodulation         : 0.19
% 5.92/2.10  BG Simplification    : 0.04
% 5.92/2.10  Subsumption          : 0.30
% 5.92/2.10  Abstraction          : 0.05
% 5.92/2.10  MUC search           : 0.00
% 5.92/2.10  Cooper               : 0.00
% 5.92/2.10  Total                : 1.41
% 5.92/2.10  Index Insertion      : 0.00
% 5.92/2.10  Index Deletion       : 0.00
% 5.92/2.10  Index Matching       : 0.00
% 5.92/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
