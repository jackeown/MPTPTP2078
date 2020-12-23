%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:04 EST 2020

% Result     : Theorem 4.58s
% Output     : CNFRefutation 4.97s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 209 expanded)
%              Number of leaves         :   36 (  86 expanded)
%              Depth                    :   14
%              Number of atoms          :  246 ( 714 expanded)
%              Number of equality atoms :   27 (  60 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k3_yellow_0 > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v1_yellow_0,type,(
    v1_yellow_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_135,negated_conjecture,(
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

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                <=> r2_hidden(D,C) ) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(k3_yellow_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_80,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,k3_yellow_0(A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).

tff(f_99,axiom,(
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

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_69,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_40,plain,(
    ! [B_49] :
      ( ~ v1_subset_1(B_49,B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_71,plain,(
    ! [B_49] : ~ v1_subset_1(B_49,B_49) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_40])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_8,plain,(
    ! [A_7,B_8,C_12] :
      ( m1_subset_1('#skF_1'(A_7,B_8,C_12),A_7)
      | C_12 = B_8
      | ~ m1_subset_1(C_12,k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_44,plain,(
    v13_waybel_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_86,plain,(
    ! [A_55,B_56] :
      ( r2_hidden(A_55,B_56)
      | v1_xboole_0(B_56)
      | ~ m1_subset_1(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_62,plain,
    ( r2_hidden(k3_yellow_0('#skF_4'),'#skF_5')
    | ~ v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_84,plain,(
    ~ v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_68,plain,
    ( v1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_85,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_68])).

tff(c_89,plain,
    ( v1_xboole_0('#skF_5')
    | ~ m1_subset_1(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_85])).

tff(c_92,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_89])).

tff(c_50,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_93,plain,(
    ! [B_57,A_58] :
      ( v1_subset_1(B_57,A_58)
      | B_57 = A_58
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_96,plain,
    ( v1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | u1_struct_0('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_42,c_93])).

tff(c_102,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_96])).

tff(c_22,plain,(
    ! [A_19] :
      ( m1_subset_1(k3_yellow_0(A_19),u1_struct_0(A_19))
      | ~ l1_orders_2(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_113,plain,
    ( m1_subset_1(k3_yellow_0('#skF_4'),'#skF_5')
    | ~ l1_orders_2('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_22])).

tff(c_117,plain,(
    m1_subset_1(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_113])).

tff(c_119,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_117])).

tff(c_120,plain,(
    r2_hidden(k3_yellow_0('#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_54,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_52,plain,(
    v1_yellow_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_149,plain,(
    ! [A_67,C_68,B_69] :
      ( m1_subset_1(A_67,C_68)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(C_68))
      | ~ r2_hidden(A_67,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_154,plain,(
    ! [A_67] :
      ( m1_subset_1(A_67,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_67,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_42,c_149])).

tff(c_24,plain,(
    ! [A_20,B_22] :
      ( r1_orders_2(A_20,k3_yellow_0(A_20),B_22)
      | ~ m1_subset_1(B_22,u1_struct_0(A_20))
      | ~ l1_orders_2(A_20)
      | ~ v1_yellow_0(A_20)
      | ~ v5_orders_2(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_775,plain,(
    ! [D_150,B_151,A_152,C_153] :
      ( r2_hidden(D_150,B_151)
      | ~ r1_orders_2(A_152,C_153,D_150)
      | ~ r2_hidden(C_153,B_151)
      | ~ m1_subset_1(D_150,u1_struct_0(A_152))
      | ~ m1_subset_1(C_153,u1_struct_0(A_152))
      | ~ v13_waybel_0(B_151,A_152)
      | ~ m1_subset_1(B_151,k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ l1_orders_2(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1455,plain,(
    ! [B_217,B_218,A_219] :
      ( r2_hidden(B_217,B_218)
      | ~ r2_hidden(k3_yellow_0(A_219),B_218)
      | ~ m1_subset_1(k3_yellow_0(A_219),u1_struct_0(A_219))
      | ~ v13_waybel_0(B_218,A_219)
      | ~ m1_subset_1(B_218,k1_zfmisc_1(u1_struct_0(A_219)))
      | ~ m1_subset_1(B_217,u1_struct_0(A_219))
      | ~ l1_orders_2(A_219)
      | ~ v1_yellow_0(A_219)
      | ~ v5_orders_2(A_219)
      | v2_struct_0(A_219) ) ),
    inference(resolution,[status(thm)],[c_24,c_775])).

tff(c_1466,plain,(
    ! [B_217,B_218] :
      ( r2_hidden(B_217,B_218)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_218)
      | ~ v13_waybel_0(B_218,'#skF_4')
      | ~ m1_subset_1(B_218,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_217,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v1_yellow_0('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_154,c_1455])).

tff(c_1483,plain,(
    ! [B_217,B_218] :
      ( r2_hidden(B_217,B_218)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_218)
      | ~ v13_waybel_0(B_218,'#skF_4')
      | ~ m1_subset_1(B_218,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_217,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_54,c_52,c_50,c_1466])).

tff(c_1486,plain,(
    ! [B_220,B_221] :
      ( r2_hidden(B_220,B_221)
      | ~ r2_hidden(k3_yellow_0('#skF_4'),B_221)
      | ~ v13_waybel_0(B_221,'#skF_4')
      | ~ m1_subset_1(B_221,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_220,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1483])).

tff(c_1518,plain,(
    ! [B_220] :
      ( r2_hidden(B_220,'#skF_5')
      | ~ r2_hidden(k3_yellow_0('#skF_4'),'#skF_5')
      | ~ v13_waybel_0('#skF_5','#skF_4')
      | ~ m1_subset_1(B_220,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_42,c_1486])).

tff(c_1538,plain,(
    ! [B_222] :
      ( r2_hidden(B_222,'#skF_5')
      | ~ m1_subset_1(B_222,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_120,c_1518])).

tff(c_1871,plain,(
    ! [B_236,C_237] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_4'),B_236,C_237),'#skF_5')
      | C_237 = B_236
      | ~ m1_subset_1(C_237,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_236,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_8,c_1538])).

tff(c_480,plain,(
    ! [A_128,B_129,C_130] :
      ( r2_hidden('#skF_1'(A_128,B_129,C_130),B_129)
      | r2_hidden('#skF_1'(A_128,B_129,C_130),C_130)
      | C_130 = B_129
      | ~ m1_subset_1(C_130,k1_zfmisc_1(A_128))
      | ~ m1_subset_1(B_129,k1_zfmisc_1(A_128)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6,plain,(
    ! [C_6,A_3,B_4] :
      ( r2_hidden(C_6,A_3)
      | ~ r2_hidden(C_6,B_4)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_509,plain,(
    ! [A_128,B_129,C_130,A_3] :
      ( r2_hidden('#skF_1'(A_128,B_129,C_130),A_3)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(A_3))
      | r2_hidden('#skF_1'(A_128,B_129,C_130),C_130)
      | C_130 = B_129
      | ~ m1_subset_1(C_130,k1_zfmisc_1(A_128))
      | ~ m1_subset_1(B_129,k1_zfmisc_1(A_128)) ) ),
    inference(resolution,[status(thm)],[c_480,c_6])).

tff(c_921,plain,(
    ! [B_182,A_183,A_184] :
      ( ~ m1_subset_1(B_182,k1_zfmisc_1(A_183))
      | B_182 = A_183
      | ~ m1_subset_1(A_183,k1_zfmisc_1(A_184))
      | ~ m1_subset_1(B_182,k1_zfmisc_1(A_184))
      | r2_hidden('#skF_1'(A_184,B_182,A_183),A_183) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_509])).

tff(c_10,plain,(
    ! [A_7,B_8,C_12] :
      ( ~ r2_hidden('#skF_1'(A_7,B_8,C_12),C_12)
      | ~ r2_hidden('#skF_1'(A_7,B_8,C_12),B_8)
      | C_12 = B_8
      | ~ m1_subset_1(C_12,k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_955,plain,(
    ! [A_184,B_182,A_183] :
      ( ~ r2_hidden('#skF_1'(A_184,B_182,A_183),B_182)
      | ~ m1_subset_1(B_182,k1_zfmisc_1(A_183))
      | B_182 = A_183
      | ~ m1_subset_1(A_183,k1_zfmisc_1(A_184))
      | ~ m1_subset_1(B_182,k1_zfmisc_1(A_184)) ) ),
    inference(resolution,[status(thm)],[c_921,c_10])).

tff(c_1875,plain,(
    ! [C_237] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(C_237))
      | C_237 = '#skF_5'
      | ~ m1_subset_1(C_237,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_1871,c_955])).

tff(c_1921,plain,(
    ! [C_241] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(C_241))
      | C_241 = '#skF_5'
      | ~ m1_subset_1(C_241,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1875])).

tff(c_1968,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | u1_struct_0('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_69,c_1921])).

tff(c_1985,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1968])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( r2_hidden(A_14,B_15)
      | v1_xboole_0(B_15)
      | ~ m1_subset_1(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_138,plain,(
    ! [C_63,A_64,B_65] :
      ( r2_hidden(C_63,A_64)
      | ~ r2_hidden(C_63,B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_180,plain,(
    ! [A_74,A_75,B_76] :
      ( r2_hidden(A_74,A_75)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_75))
      | v1_xboole_0(B_76)
      | ~ m1_subset_1(A_74,B_76) ) ),
    inference(resolution,[status(thm)],[c_18,c_138])).

tff(c_185,plain,(
    ! [A_74] :
      ( r2_hidden(A_74,u1_struct_0('#skF_4'))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(A_74,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_42,c_180])).

tff(c_191,plain,(
    ! [A_74] :
      ( r2_hidden(A_74,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_74,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_185])).

tff(c_455,plain,(
    ! [A_125,B_126,C_127] :
      ( ~ r2_hidden('#skF_1'(A_125,B_126,C_127),C_127)
      | ~ r2_hidden('#skF_1'(A_125,B_126,C_127),B_126)
      | C_127 = B_126
      | ~ m1_subset_1(C_127,k1_zfmisc_1(A_125))
      | ~ m1_subset_1(B_126,k1_zfmisc_1(A_125)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_816,plain,(
    ! [A_166,B_167,B_168] :
      ( ~ r2_hidden('#skF_1'(A_166,B_167,B_168),B_167)
      | B_168 = B_167
      | ~ m1_subset_1(B_168,k1_zfmisc_1(A_166))
      | ~ m1_subset_1(B_167,k1_zfmisc_1(A_166))
      | v1_xboole_0(B_168)
      | ~ m1_subset_1('#skF_1'(A_166,B_167,B_168),B_168) ) ),
    inference(resolution,[status(thm)],[c_18,c_455])).

tff(c_960,plain,(
    ! [B_185,A_186] :
      ( u1_struct_0('#skF_4') = B_185
      | ~ m1_subset_1(B_185,k1_zfmisc_1(A_186))
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_186))
      | v1_xboole_0(B_185)
      | ~ m1_subset_1('#skF_1'(A_186,u1_struct_0('#skF_4'),B_185),B_185)
      | ~ m1_subset_1('#skF_1'(A_186,u1_struct_0('#skF_4'),B_185),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_191,c_816])).

tff(c_971,plain,(
    ! [A_7] :
      ( v1_xboole_0(A_7)
      | ~ m1_subset_1('#skF_1'(A_7,u1_struct_0('#skF_4'),A_7),'#skF_5')
      | u1_struct_0('#skF_4') = A_7
      | ~ m1_subset_1(A_7,k1_zfmisc_1(A_7))
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_7)) ) ),
    inference(resolution,[status(thm)],[c_8,c_960])).

tff(c_987,plain,(
    ! [A_187] :
      ( v1_xboole_0(A_187)
      | ~ m1_subset_1('#skF_1'(A_187,u1_struct_0('#skF_4'),A_187),'#skF_5')
      | u1_struct_0('#skF_4') = A_187
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_187)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_971])).

tff(c_995,plain,
    ( v1_xboole_0('#skF_5')
    | u1_struct_0('#skF_4') = '#skF_5'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5'))
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_8,c_987])).

tff(c_998,plain,
    ( v1_xboole_0('#skF_5')
    | u1_struct_0('#skF_4') = '#skF_5'
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_995])).

tff(c_999,plain,
    ( u1_struct_0('#skF_4') = '#skF_5'
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_998])).

tff(c_1000,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_999])).

tff(c_1998,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1985,c_1000])).

tff(c_2021,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_1998])).

tff(c_2022,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_999])).

tff(c_121,plain,(
    v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_2041,plain,(
    v1_subset_1('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2022,c_121])).

tff(c_2046,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_2041])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:54:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.58/1.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.58/1.89  
% 4.58/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.58/1.89  %$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k3_yellow_0 > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 4.58/1.89  
% 4.58/1.89  %Foreground sorts:
% 4.58/1.89  
% 4.58/1.89  
% 4.58/1.89  %Background operators:
% 4.58/1.89  
% 4.58/1.89  
% 4.58/1.89  %Foreground operators:
% 4.58/1.89  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.58/1.89  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.58/1.89  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.58/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.58/1.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.58/1.89  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.58/1.89  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 4.58/1.89  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 4.58/1.89  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 4.58/1.89  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.58/1.89  tff('#skF_5', type, '#skF_5': $i).
% 4.58/1.89  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.58/1.89  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 4.58/1.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.58/1.89  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.58/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.58/1.89  tff('#skF_4', type, '#skF_4': $i).
% 4.58/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.58/1.89  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.58/1.89  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 4.58/1.89  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.58/1.89  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.58/1.89  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.58/1.89  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 4.58/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.58/1.89  
% 4.97/1.91  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.97/1.91  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.97/1.91  tff(f_106, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 4.97/1.91  tff(f_135, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_subset_1(B, u1_struct_0(A)) <=> ~r2_hidden(k3_yellow_0(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_7)).
% 4.97/1.91  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_subset_1)).
% 4.97/1.91  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.97/1.91  tff(f_66, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(k3_yellow_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow_0)).
% 4.97/1.91  tff(f_62, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 4.97/1.91  tff(f_80, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, k3_yellow_0(A), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_yellow_0)).
% 4.97/1.91  tff(f_99, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v13_waybel_0(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r1_orders_2(A, C, D)) => r2_hidden(D, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_waybel_0)).
% 4.97/1.91  tff(f_36, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 4.97/1.91  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.97/1.91  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.97/1.91  tff(c_69, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 4.97/1.91  tff(c_40, plain, (![B_49]: (~v1_subset_1(B_49, B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(B_49)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.97/1.91  tff(c_71, plain, (![B_49]: (~v1_subset_1(B_49, B_49))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_40])).
% 4.97/1.91  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.97/1.91  tff(c_8, plain, (![A_7, B_8, C_12]: (m1_subset_1('#skF_1'(A_7, B_8, C_12), A_7) | C_12=B_8 | ~m1_subset_1(C_12, k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.97/1.91  tff(c_44, plain, (v13_waybel_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.97/1.91  tff(c_48, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.97/1.91  tff(c_86, plain, (![A_55, B_56]: (r2_hidden(A_55, B_56) | v1_xboole_0(B_56) | ~m1_subset_1(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.97/1.91  tff(c_62, plain, (r2_hidden(k3_yellow_0('#skF_4'), '#skF_5') | ~v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.97/1.91  tff(c_84, plain, (~v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_62])).
% 4.97/1.91  tff(c_68, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.97/1.91  tff(c_85, plain, (~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_84, c_68])).
% 4.97/1.91  tff(c_89, plain, (v1_xboole_0('#skF_5') | ~m1_subset_1(k3_yellow_0('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_86, c_85])).
% 4.97/1.91  tff(c_92, plain, (~m1_subset_1(k3_yellow_0('#skF_4'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_48, c_89])).
% 4.97/1.91  tff(c_50, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.97/1.91  tff(c_93, plain, (![B_57, A_58]: (v1_subset_1(B_57, A_58) | B_57=A_58 | ~m1_subset_1(B_57, k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.97/1.91  tff(c_96, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4')) | u1_struct_0('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_42, c_93])).
% 4.97/1.91  tff(c_102, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_84, c_96])).
% 4.97/1.91  tff(c_22, plain, (![A_19]: (m1_subset_1(k3_yellow_0(A_19), u1_struct_0(A_19)) | ~l1_orders_2(A_19))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.97/1.91  tff(c_113, plain, (m1_subset_1(k3_yellow_0('#skF_4'), '#skF_5') | ~l1_orders_2('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_102, c_22])).
% 4.97/1.91  tff(c_117, plain, (m1_subset_1(k3_yellow_0('#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_113])).
% 4.97/1.91  tff(c_119, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_117])).
% 4.97/1.91  tff(c_120, plain, (r2_hidden(k3_yellow_0('#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_62])).
% 4.97/1.91  tff(c_60, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.97/1.91  tff(c_54, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.97/1.91  tff(c_52, plain, (v1_yellow_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.97/1.91  tff(c_149, plain, (![A_67, C_68, B_69]: (m1_subset_1(A_67, C_68) | ~m1_subset_1(B_69, k1_zfmisc_1(C_68)) | ~r2_hidden(A_67, B_69))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.97/1.91  tff(c_154, plain, (![A_67]: (m1_subset_1(A_67, u1_struct_0('#skF_4')) | ~r2_hidden(A_67, '#skF_5'))), inference(resolution, [status(thm)], [c_42, c_149])).
% 4.97/1.91  tff(c_24, plain, (![A_20, B_22]: (r1_orders_2(A_20, k3_yellow_0(A_20), B_22) | ~m1_subset_1(B_22, u1_struct_0(A_20)) | ~l1_orders_2(A_20) | ~v1_yellow_0(A_20) | ~v5_orders_2(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.97/1.91  tff(c_775, plain, (![D_150, B_151, A_152, C_153]: (r2_hidden(D_150, B_151) | ~r1_orders_2(A_152, C_153, D_150) | ~r2_hidden(C_153, B_151) | ~m1_subset_1(D_150, u1_struct_0(A_152)) | ~m1_subset_1(C_153, u1_struct_0(A_152)) | ~v13_waybel_0(B_151, A_152) | ~m1_subset_1(B_151, k1_zfmisc_1(u1_struct_0(A_152))) | ~l1_orders_2(A_152))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.97/1.91  tff(c_1455, plain, (![B_217, B_218, A_219]: (r2_hidden(B_217, B_218) | ~r2_hidden(k3_yellow_0(A_219), B_218) | ~m1_subset_1(k3_yellow_0(A_219), u1_struct_0(A_219)) | ~v13_waybel_0(B_218, A_219) | ~m1_subset_1(B_218, k1_zfmisc_1(u1_struct_0(A_219))) | ~m1_subset_1(B_217, u1_struct_0(A_219)) | ~l1_orders_2(A_219) | ~v1_yellow_0(A_219) | ~v5_orders_2(A_219) | v2_struct_0(A_219))), inference(resolution, [status(thm)], [c_24, c_775])).
% 4.97/1.91  tff(c_1466, plain, (![B_217, B_218]: (r2_hidden(B_217, B_218) | ~r2_hidden(k3_yellow_0('#skF_4'), B_218) | ~v13_waybel_0(B_218, '#skF_4') | ~m1_subset_1(B_218, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_217, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v1_yellow_0('#skF_4') | ~v5_orders_2('#skF_4') | v2_struct_0('#skF_4') | ~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5'))), inference(resolution, [status(thm)], [c_154, c_1455])).
% 4.97/1.91  tff(c_1483, plain, (![B_217, B_218]: (r2_hidden(B_217, B_218) | ~r2_hidden(k3_yellow_0('#skF_4'), B_218) | ~v13_waybel_0(B_218, '#skF_4') | ~m1_subset_1(B_218, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_217, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_54, c_52, c_50, c_1466])).
% 4.97/1.91  tff(c_1486, plain, (![B_220, B_221]: (r2_hidden(B_220, B_221) | ~r2_hidden(k3_yellow_0('#skF_4'), B_221) | ~v13_waybel_0(B_221, '#skF_4') | ~m1_subset_1(B_221, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_220, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_60, c_1483])).
% 4.97/1.91  tff(c_1518, plain, (![B_220]: (r2_hidden(B_220, '#skF_5') | ~r2_hidden(k3_yellow_0('#skF_4'), '#skF_5') | ~v13_waybel_0('#skF_5', '#skF_4') | ~m1_subset_1(B_220, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_42, c_1486])).
% 4.97/1.91  tff(c_1538, plain, (![B_222]: (r2_hidden(B_222, '#skF_5') | ~m1_subset_1(B_222, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_120, c_1518])).
% 4.97/1.91  tff(c_1871, plain, (![B_236, C_237]: (r2_hidden('#skF_1'(u1_struct_0('#skF_4'), B_236, C_237), '#skF_5') | C_237=B_236 | ~m1_subset_1(C_237, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_236, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_8, c_1538])).
% 4.97/1.91  tff(c_480, plain, (![A_128, B_129, C_130]: (r2_hidden('#skF_1'(A_128, B_129, C_130), B_129) | r2_hidden('#skF_1'(A_128, B_129, C_130), C_130) | C_130=B_129 | ~m1_subset_1(C_130, k1_zfmisc_1(A_128)) | ~m1_subset_1(B_129, k1_zfmisc_1(A_128)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.97/1.91  tff(c_6, plain, (![C_6, A_3, B_4]: (r2_hidden(C_6, A_3) | ~r2_hidden(C_6, B_4) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.97/1.91  tff(c_509, plain, (![A_128, B_129, C_130, A_3]: (r2_hidden('#skF_1'(A_128, B_129, C_130), A_3) | ~m1_subset_1(B_129, k1_zfmisc_1(A_3)) | r2_hidden('#skF_1'(A_128, B_129, C_130), C_130) | C_130=B_129 | ~m1_subset_1(C_130, k1_zfmisc_1(A_128)) | ~m1_subset_1(B_129, k1_zfmisc_1(A_128)))), inference(resolution, [status(thm)], [c_480, c_6])).
% 4.97/1.91  tff(c_921, plain, (![B_182, A_183, A_184]: (~m1_subset_1(B_182, k1_zfmisc_1(A_183)) | B_182=A_183 | ~m1_subset_1(A_183, k1_zfmisc_1(A_184)) | ~m1_subset_1(B_182, k1_zfmisc_1(A_184)) | r2_hidden('#skF_1'(A_184, B_182, A_183), A_183))), inference(factorization, [status(thm), theory('equality')], [c_509])).
% 4.97/1.91  tff(c_10, plain, (![A_7, B_8, C_12]: (~r2_hidden('#skF_1'(A_7, B_8, C_12), C_12) | ~r2_hidden('#skF_1'(A_7, B_8, C_12), B_8) | C_12=B_8 | ~m1_subset_1(C_12, k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.97/1.91  tff(c_955, plain, (![A_184, B_182, A_183]: (~r2_hidden('#skF_1'(A_184, B_182, A_183), B_182) | ~m1_subset_1(B_182, k1_zfmisc_1(A_183)) | B_182=A_183 | ~m1_subset_1(A_183, k1_zfmisc_1(A_184)) | ~m1_subset_1(B_182, k1_zfmisc_1(A_184)))), inference(resolution, [status(thm)], [c_921, c_10])).
% 4.97/1.91  tff(c_1875, plain, (![C_237]: (~m1_subset_1('#skF_5', k1_zfmisc_1(C_237)) | C_237='#skF_5' | ~m1_subset_1(C_237, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_1871, c_955])).
% 4.97/1.91  tff(c_1921, plain, (![C_241]: (~m1_subset_1('#skF_5', k1_zfmisc_1(C_241)) | C_241='#skF_5' | ~m1_subset_1(C_241, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1875])).
% 4.97/1.91  tff(c_1968, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | u1_struct_0('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_69, c_1921])).
% 4.97/1.91  tff(c_1985, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1968])).
% 4.97/1.91  tff(c_18, plain, (![A_14, B_15]: (r2_hidden(A_14, B_15) | v1_xboole_0(B_15) | ~m1_subset_1(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.97/1.91  tff(c_138, plain, (![C_63, A_64, B_65]: (r2_hidden(C_63, A_64) | ~r2_hidden(C_63, B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.97/1.91  tff(c_180, plain, (![A_74, A_75, B_76]: (r2_hidden(A_74, A_75) | ~m1_subset_1(B_76, k1_zfmisc_1(A_75)) | v1_xboole_0(B_76) | ~m1_subset_1(A_74, B_76))), inference(resolution, [status(thm)], [c_18, c_138])).
% 4.97/1.91  tff(c_185, plain, (![A_74]: (r2_hidden(A_74, u1_struct_0('#skF_4')) | v1_xboole_0('#skF_5') | ~m1_subset_1(A_74, '#skF_5'))), inference(resolution, [status(thm)], [c_42, c_180])).
% 4.97/1.91  tff(c_191, plain, (![A_74]: (r2_hidden(A_74, u1_struct_0('#skF_4')) | ~m1_subset_1(A_74, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_48, c_185])).
% 4.97/1.91  tff(c_455, plain, (![A_125, B_126, C_127]: (~r2_hidden('#skF_1'(A_125, B_126, C_127), C_127) | ~r2_hidden('#skF_1'(A_125, B_126, C_127), B_126) | C_127=B_126 | ~m1_subset_1(C_127, k1_zfmisc_1(A_125)) | ~m1_subset_1(B_126, k1_zfmisc_1(A_125)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.97/1.91  tff(c_816, plain, (![A_166, B_167, B_168]: (~r2_hidden('#skF_1'(A_166, B_167, B_168), B_167) | B_168=B_167 | ~m1_subset_1(B_168, k1_zfmisc_1(A_166)) | ~m1_subset_1(B_167, k1_zfmisc_1(A_166)) | v1_xboole_0(B_168) | ~m1_subset_1('#skF_1'(A_166, B_167, B_168), B_168))), inference(resolution, [status(thm)], [c_18, c_455])).
% 4.97/1.91  tff(c_960, plain, (![B_185, A_186]: (u1_struct_0('#skF_4')=B_185 | ~m1_subset_1(B_185, k1_zfmisc_1(A_186)) | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_186)) | v1_xboole_0(B_185) | ~m1_subset_1('#skF_1'(A_186, u1_struct_0('#skF_4'), B_185), B_185) | ~m1_subset_1('#skF_1'(A_186, u1_struct_0('#skF_4'), B_185), '#skF_5'))), inference(resolution, [status(thm)], [c_191, c_816])).
% 4.97/1.91  tff(c_971, plain, (![A_7]: (v1_xboole_0(A_7) | ~m1_subset_1('#skF_1'(A_7, u1_struct_0('#skF_4'), A_7), '#skF_5') | u1_struct_0('#skF_4')=A_7 | ~m1_subset_1(A_7, k1_zfmisc_1(A_7)) | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_7)))), inference(resolution, [status(thm)], [c_8, c_960])).
% 4.97/1.91  tff(c_987, plain, (![A_187]: (v1_xboole_0(A_187) | ~m1_subset_1('#skF_1'(A_187, u1_struct_0('#skF_4'), A_187), '#skF_5') | u1_struct_0('#skF_4')=A_187 | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_187)))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_971])).
% 4.97/1.91  tff(c_995, plain, (v1_xboole_0('#skF_5') | u1_struct_0('#skF_4')='#skF_5' | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5')) | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_8, c_987])).
% 4.97/1.91  tff(c_998, plain, (v1_xboole_0('#skF_5') | u1_struct_0('#skF_4')='#skF_5' | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_995])).
% 4.97/1.91  tff(c_999, plain, (u1_struct_0('#skF_4')='#skF_5' | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_48, c_998])).
% 4.97/1.91  tff(c_1000, plain, (~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_999])).
% 4.97/1.91  tff(c_1998, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1985, c_1000])).
% 4.97/1.91  tff(c_2021, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69, c_1998])).
% 4.97/1.91  tff(c_2022, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_999])).
% 4.97/1.91  tff(c_121, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_62])).
% 4.97/1.91  tff(c_2041, plain, (v1_subset_1('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2022, c_121])).
% 4.97/1.91  tff(c_2046, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_2041])).
% 4.97/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.97/1.91  
% 4.97/1.91  Inference rules
% 4.97/1.91  ----------------------
% 4.97/1.91  #Ref     : 0
% 4.97/1.91  #Sup     : 378
% 4.97/1.91  #Fact    : 8
% 4.97/1.91  #Define  : 0
% 4.97/1.91  #Split   : 8
% 4.97/1.91  #Chain   : 0
% 4.97/1.91  #Close   : 0
% 4.97/1.91  
% 4.97/1.91  Ordering : KBO
% 4.97/1.91  
% 4.97/1.91  Simplification rules
% 4.97/1.91  ----------------------
% 4.97/1.91  #Subsume      : 63
% 4.97/1.91  #Demod        : 170
% 4.97/1.91  #Tautology    : 60
% 4.97/1.91  #SimpNegUnit  : 18
% 4.97/1.91  #BackRed      : 51
% 4.97/1.91  
% 4.97/1.91  #Partial instantiations: 0
% 4.97/1.91  #Strategies tried      : 1
% 4.97/1.91  
% 4.97/1.91  Timing (in seconds)
% 4.97/1.91  ----------------------
% 4.97/1.92  Preprocessing        : 0.33
% 4.97/1.92  Parsing              : 0.18
% 4.97/1.92  CNF conversion       : 0.03
% 4.97/1.92  Main loop            : 0.77
% 4.97/1.92  Inferencing          : 0.26
% 4.97/1.92  Reduction            : 0.20
% 4.97/1.92  Demodulation         : 0.14
% 4.97/1.92  BG Simplification    : 0.03
% 4.97/1.92  Subsumption          : 0.22
% 4.97/1.92  Abstraction          : 0.04
% 4.97/1.92  MUC search           : 0.00
% 4.97/1.92  Cooper               : 0.00
% 4.97/1.92  Total                : 1.14
% 4.97/1.92  Index Insertion      : 0.00
% 4.97/1.92  Index Deletion       : 0.00
% 4.97/1.92  Index Matching       : 0.00
% 4.97/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
