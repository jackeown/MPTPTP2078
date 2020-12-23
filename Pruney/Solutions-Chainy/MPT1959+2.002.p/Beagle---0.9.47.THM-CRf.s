%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:57 EST 2020

% Result     : Theorem 4.06s
% Output     : CNFRefutation 4.06s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 640 expanded)
%              Number of leaves         :   38 ( 237 expanded)
%              Depth                    :   18
%              Number of atoms          :  233 (2880 expanded)
%              Number of equality atoms :   32 ( 110 expanded)
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

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

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
    ! [B_46] :
      ( ~ v1_subset_1(B_46,B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_71,plain,(
    ! [B_46] : ~ v1_subset_1(B_46,B_46) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_40])).

tff(c_204,plain,(
    ! [A_76,B_77] :
      ( r2_hidden('#skF_1'(A_76,B_77),B_77)
      | r2_hidden('#skF_2'(A_76,B_77),A_76)
      | B_77 = A_76 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_238,plain,(
    ! [A_82,B_83] :
      ( m1_subset_1('#skF_1'(A_82,B_83),B_83)
      | r2_hidden('#skF_2'(A_82,B_83),A_82)
      | B_83 = A_82 ) ),
    inference(resolution,[status(thm)],[c_204,c_16])).

tff(c_266,plain,(
    ! [A_82,B_83] :
      ( m1_subset_1('#skF_2'(A_82,B_83),A_82)
      | m1_subset_1('#skF_1'(A_82,B_83),B_83)
      | B_83 = A_82 ) ),
    inference(resolution,[status(thm)],[c_238,c_16])).

tff(c_44,plain,(
    v13_waybel_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_98,plain,(
    ! [A_56,B_57] :
      ( r2_hidden(A_56,B_57)
      | v1_xboole_0(B_57)
      | ~ m1_subset_1(A_56,B_57) ) ),
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

tff(c_97,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_68])).

tff(c_101,plain,
    ( v1_xboole_0('#skF_6')
    | ~ m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_98,c_97])).

tff(c_107,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_101])).

tff(c_50,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_109,plain,(
    ! [B_58,A_59] :
      ( v1_subset_1(B_58,A_59)
      | B_58 = A_59
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_112,plain,
    ( v1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_42,c_109])).

tff(c_118,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_112])).

tff(c_22,plain,(
    ! [A_16] :
      ( m1_subset_1(k3_yellow_0(A_16),u1_struct_0(A_16))
      | ~ l1_orders_2(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_130,plain,
    ( m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6')
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_22])).

tff(c_134,plain,(
    m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_130])).

tff(c_136,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_134])).

tff(c_137,plain,(
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

tff(c_174,plain,(
    ! [A_66,C_67,B_68] :
      ( m1_subset_1(A_66,C_67)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(C_67))
      | ~ r2_hidden(A_66,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_179,plain,(
    ! [A_66] :
      ( m1_subset_1(A_66,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_66,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_42,c_174])).

tff(c_24,plain,(
    ! [A_17,B_19] :
      ( r1_orders_2(A_17,k3_yellow_0(A_17),B_19)
      | ~ m1_subset_1(B_19,u1_struct_0(A_17))
      | ~ l1_orders_2(A_17)
      | ~ v1_yellow_0(A_17)
      | ~ v5_orders_2(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_787,plain,(
    ! [D_138,B_139,A_140,C_141] :
      ( r2_hidden(D_138,B_139)
      | ~ r1_orders_2(A_140,C_141,D_138)
      | ~ r2_hidden(C_141,B_139)
      | ~ m1_subset_1(D_138,u1_struct_0(A_140))
      | ~ m1_subset_1(C_141,u1_struct_0(A_140))
      | ~ v13_waybel_0(B_139,A_140)
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ l1_orders_2(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_945,plain,(
    ! [B_155,B_156,A_157] :
      ( r2_hidden(B_155,B_156)
      | ~ r2_hidden(k3_yellow_0(A_157),B_156)
      | ~ m1_subset_1(k3_yellow_0(A_157),u1_struct_0(A_157))
      | ~ v13_waybel_0(B_156,A_157)
      | ~ m1_subset_1(B_156,k1_zfmisc_1(u1_struct_0(A_157)))
      | ~ m1_subset_1(B_155,u1_struct_0(A_157))
      | ~ l1_orders_2(A_157)
      | ~ v1_yellow_0(A_157)
      | ~ v5_orders_2(A_157)
      | v2_struct_0(A_157) ) ),
    inference(resolution,[status(thm)],[c_24,c_787])).

tff(c_948,plain,(
    ! [B_155,B_156] :
      ( r2_hidden(B_155,B_156)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_156)
      | ~ v13_waybel_0(B_156,'#skF_5')
      | ~ m1_subset_1(B_156,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_155,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v1_yellow_0('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_179,c_945])).

tff(c_953,plain,(
    ! [B_155,B_156] :
      ( r2_hidden(B_155,B_156)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_156)
      | ~ v13_waybel_0(B_156,'#skF_5')
      | ~ m1_subset_1(B_156,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_155,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_54,c_52,c_50,c_948])).

tff(c_956,plain,(
    ! [B_158,B_159] :
      ( r2_hidden(B_158,B_159)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_159)
      | ~ v13_waybel_0(B_159,'#skF_5')
      | ~ m1_subset_1(B_159,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_158,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_953])).

tff(c_985,plain,(
    ! [B_158] :
      ( r2_hidden(B_158,'#skF_6')
      | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
      | ~ v13_waybel_0('#skF_6','#skF_5')
      | ~ m1_subset_1(B_158,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_42,c_956])).

tff(c_1002,plain,(
    ! [B_160] :
      ( r2_hidden(B_160,'#skF_6')
      | ~ m1_subset_1(B_160,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_137,c_985])).

tff(c_1332,plain,(
    ! [A_169] :
      ( r2_hidden('#skF_1'(A_169,u1_struct_0('#skF_5')),'#skF_6')
      | m1_subset_1('#skF_2'(A_169,u1_struct_0('#skF_5')),A_169)
      | u1_struct_0('#skF_5') = A_169 ) ),
    inference(resolution,[status(thm)],[c_266,c_1002])).

tff(c_193,plain,(
    ! [A_74,B_75] :
      ( ~ r2_hidden('#skF_1'(A_74,B_75),A_74)
      | r2_hidden('#skF_2'(A_74,B_75),A_74)
      | B_75 = A_74 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_203,plain,(
    ! [A_74,B_75] :
      ( m1_subset_1('#skF_2'(A_74,B_75),A_74)
      | ~ r2_hidden('#skF_1'(A_74,B_75),A_74)
      | B_75 = A_74 ) ),
    inference(resolution,[status(thm)],[c_193,c_16])).

tff(c_1382,plain,
    ( m1_subset_1('#skF_2'('#skF_6',u1_struct_0('#skF_5')),'#skF_6')
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1332,c_203])).

tff(c_1403,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1382])).

tff(c_138,plain,(
    v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_1419,plain,(
    v1_subset_1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1403,c_138])).

tff(c_1423,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_1419])).

tff(c_1425,plain,(
    u1_struct_0('#skF_5') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1382])).

tff(c_216,plain,(
    ! [A_76,B_77] :
      ( m1_subset_1('#skF_1'(A_76,B_77),B_77)
      | r2_hidden('#skF_2'(A_76,B_77),A_76)
      | B_77 = A_76 ) ),
    inference(resolution,[status(thm)],[c_204,c_16])).

tff(c_1081,plain,(
    ! [A_76] :
      ( r2_hidden('#skF_1'(A_76,u1_struct_0('#skF_5')),'#skF_6')
      | r2_hidden('#skF_2'(A_76,u1_struct_0('#skF_5')),A_76)
      | u1_struct_0('#skF_5') = A_76 ) ),
    inference(resolution,[status(thm)],[c_216,c_1002])).

tff(c_145,plain,(
    ! [B_60,A_61] :
      ( v1_xboole_0(B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_61))
      | ~ v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_148,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_42,c_145])).

tff(c_154,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_148])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( r2_hidden(A_11,B_12)
      | v1_xboole_0(B_12)
      | ~ m1_subset_1(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_187,plain,(
    ! [A_72,B_73] :
      ( r2_hidden('#skF_1'(A_72,B_73),B_73)
      | ~ r2_hidden('#skF_2'(A_72,B_73),B_73)
      | B_73 = A_72 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_367,plain,(
    ! [A_94,B_95] :
      ( r2_hidden('#skF_1'(A_94,B_95),B_95)
      | B_95 = A_94
      | v1_xboole_0(B_95)
      | ~ m1_subset_1('#skF_2'(A_94,B_95),B_95) ) ),
    inference(resolution,[status(thm)],[c_18,c_187])).

tff(c_403,plain,(
    ! [A_100,B_101] :
      ( m1_subset_1('#skF_1'(A_100,B_101),B_101)
      | B_101 = A_100
      | v1_xboole_0(B_101)
      | ~ m1_subset_1('#skF_2'(A_100,B_101),B_101) ) ),
    inference(resolution,[status(thm)],[c_367,c_16])).

tff(c_417,plain,(
    ! [A_100] :
      ( m1_subset_1('#skF_1'(A_100,u1_struct_0('#skF_5')),u1_struct_0('#skF_5'))
      | u1_struct_0('#skF_5') = A_100
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_2'(A_100,u1_struct_0('#skF_5')),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_179,c_403])).

tff(c_424,plain,(
    ! [A_100] :
      ( m1_subset_1('#skF_1'(A_100,u1_struct_0('#skF_5')),u1_struct_0('#skF_5'))
      | u1_struct_0('#skF_5') = A_100
      | ~ r2_hidden('#skF_2'(A_100,u1_struct_0('#skF_5')),'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_417])).

tff(c_1553,plain,(
    ! [A_175] :
      ( r2_hidden('#skF_1'(A_175,u1_struct_0('#skF_5')),'#skF_6')
      | u1_struct_0('#skF_5') = A_175
      | ~ r2_hidden('#skF_2'(A_175,u1_struct_0('#skF_5')),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_424,c_1002])).

tff(c_1565,plain,
    ( r2_hidden('#skF_1'('#skF_6',u1_struct_0('#skF_5')),'#skF_6')
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1081,c_1553])).

tff(c_1581,plain,(
    r2_hidden('#skF_1'('#skF_6',u1_struct_0('#skF_5')),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_1425,c_1425,c_1565])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r2_hidden('#skF_2'(A_1,B_2),A_1)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1602,plain,(
    m1_subset_1('#skF_1'('#skF_6',u1_struct_0('#skF_5')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_1581,c_16])).

tff(c_182,plain,(
    ! [A_70,B_71] :
      ( ~ r2_hidden('#skF_1'(A_70,B_71),A_70)
      | ~ r2_hidden('#skF_2'(A_70,B_71),B_71)
      | B_71 = A_70 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_348,plain,(
    ! [B_92,B_93] :
      ( ~ r2_hidden('#skF_2'(B_92,B_93),B_93)
      | B_93 = B_92
      | v1_xboole_0(B_92)
      | ~ m1_subset_1('#skF_1'(B_92,B_93),B_92) ) ),
    inference(resolution,[status(thm)],[c_18,c_182])).

tff(c_366,plain,(
    ! [B_92,B_12] :
      ( B_92 = B_12
      | v1_xboole_0(B_92)
      | ~ m1_subset_1('#skF_1'(B_92,B_12),B_92)
      | v1_xboole_0(B_12)
      | ~ m1_subset_1('#skF_2'(B_92,B_12),B_12) ) ),
    inference(resolution,[status(thm)],[c_18,c_348])).

tff(c_1604,plain,
    ( u1_struct_0('#skF_5') = '#skF_6'
    | v1_xboole_0('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_2'('#skF_6',u1_struct_0('#skF_5')),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1602,c_366])).

tff(c_1607,plain,(
    ~ m1_subset_1('#skF_2'('#skF_6',u1_struct_0('#skF_5')),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_48,c_1425,c_1604])).

tff(c_1611,plain,(
    ~ r2_hidden('#skF_2'('#skF_6',u1_struct_0('#skF_5')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_179,c_1607])).

tff(c_1619,plain,
    ( ~ r2_hidden('#skF_1'('#skF_6',u1_struct_0('#skF_5')),'#skF_6')
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_6,c_1611])).

tff(c_1628,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1581,c_1619])).

tff(c_1630,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1425,c_1628])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:20:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.06/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.06/1.72  
% 4.06/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.06/1.73  %$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k3_yellow_0 > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 4.06/1.73  
% 4.06/1.73  %Foreground sorts:
% 4.06/1.73  
% 4.06/1.73  
% 4.06/1.73  %Background operators:
% 4.06/1.73  
% 4.06/1.73  
% 4.06/1.73  %Foreground operators:
% 4.06/1.73  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.06/1.73  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.06/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.06/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.06/1.73  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.06/1.73  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 4.06/1.73  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 4.06/1.73  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 4.06/1.73  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.06/1.73  tff('#skF_5', type, '#skF_5': $i).
% 4.06/1.73  tff('#skF_6', type, '#skF_6': $i).
% 4.06/1.73  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.06/1.73  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 4.06/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.06/1.73  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.06/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.06/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.06/1.73  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.06/1.73  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 4.06/1.73  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.06/1.73  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.06/1.73  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.06/1.73  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.06/1.73  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.06/1.73  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 4.06/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.06/1.73  
% 4.06/1.74  tff(f_34, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 4.06/1.74  tff(f_36, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.06/1.74  tff(f_103, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 4.06/1.74  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 4.06/1.74  tff(f_47, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 4.06/1.74  tff(f_132, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_subset_1(B, u1_struct_0(A)) <=> ~r2_hidden(k3_yellow_0(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_7)).
% 4.06/1.74  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 4.06/1.74  tff(f_63, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(k3_yellow_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow_0)).
% 4.06/1.74  tff(f_59, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 4.06/1.74  tff(f_77, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, k3_yellow_0(A), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_yellow_0)).
% 4.06/1.74  tff(f_96, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v13_waybel_0(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r1_orders_2(A, C, D)) => r2_hidden(D, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_waybel_0)).
% 4.06/1.74  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 4.06/1.74  tff(c_10, plain, (![A_4]: (k2_subset_1(A_4)=A_4)), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.06/1.74  tff(c_12, plain, (![A_5]: (m1_subset_1(k2_subset_1(A_5), k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.06/1.74  tff(c_69, plain, (![A_5]: (m1_subset_1(A_5, k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 4.06/1.74  tff(c_40, plain, (![B_46]: (~v1_subset_1(B_46, B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(B_46)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.06/1.74  tff(c_71, plain, (![B_46]: (~v1_subset_1(B_46, B_46))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_40])).
% 4.06/1.74  tff(c_204, plain, (![A_76, B_77]: (r2_hidden('#skF_1'(A_76, B_77), B_77) | r2_hidden('#skF_2'(A_76, B_77), A_76) | B_77=A_76)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.06/1.74  tff(c_16, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.06/1.74  tff(c_238, plain, (![A_82, B_83]: (m1_subset_1('#skF_1'(A_82, B_83), B_83) | r2_hidden('#skF_2'(A_82, B_83), A_82) | B_83=A_82)), inference(resolution, [status(thm)], [c_204, c_16])).
% 4.06/1.74  tff(c_266, plain, (![A_82, B_83]: (m1_subset_1('#skF_2'(A_82, B_83), A_82) | m1_subset_1('#skF_1'(A_82, B_83), B_83) | B_83=A_82)), inference(resolution, [status(thm)], [c_238, c_16])).
% 4.06/1.74  tff(c_44, plain, (v13_waybel_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.06/1.74  tff(c_48, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.06/1.74  tff(c_98, plain, (![A_56, B_57]: (r2_hidden(A_56, B_57) | v1_xboole_0(B_57) | ~m1_subset_1(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.06/1.74  tff(c_62, plain, (r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.06/1.74  tff(c_85, plain, (~v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_62])).
% 4.06/1.74  tff(c_68, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.06/1.74  tff(c_97, plain, (~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_85, c_68])).
% 4.06/1.74  tff(c_101, plain, (v1_xboole_0('#skF_6') | ~m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_98, c_97])).
% 4.06/1.74  tff(c_107, plain, (~m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_48, c_101])).
% 4.06/1.74  tff(c_50, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.06/1.74  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.06/1.74  tff(c_109, plain, (![B_58, A_59]: (v1_subset_1(B_58, A_59) | B_58=A_59 | ~m1_subset_1(B_58, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.06/1.74  tff(c_112, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5')) | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_42, c_109])).
% 4.06/1.74  tff(c_118, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_85, c_112])).
% 4.06/1.74  tff(c_22, plain, (![A_16]: (m1_subset_1(k3_yellow_0(A_16), u1_struct_0(A_16)) | ~l1_orders_2(A_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.06/1.74  tff(c_130, plain, (m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6') | ~l1_orders_2('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_118, c_22])).
% 4.06/1.74  tff(c_134, plain, (m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_130])).
% 4.06/1.74  tff(c_136, plain, $false, inference(negUnitSimplification, [status(thm)], [c_107, c_134])).
% 4.06/1.74  tff(c_137, plain, (r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_62])).
% 4.06/1.74  tff(c_60, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.06/1.74  tff(c_54, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.06/1.74  tff(c_52, plain, (v1_yellow_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.06/1.74  tff(c_174, plain, (![A_66, C_67, B_68]: (m1_subset_1(A_66, C_67) | ~m1_subset_1(B_68, k1_zfmisc_1(C_67)) | ~r2_hidden(A_66, B_68))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.06/1.74  tff(c_179, plain, (![A_66]: (m1_subset_1(A_66, u1_struct_0('#skF_5')) | ~r2_hidden(A_66, '#skF_6'))), inference(resolution, [status(thm)], [c_42, c_174])).
% 4.06/1.74  tff(c_24, plain, (![A_17, B_19]: (r1_orders_2(A_17, k3_yellow_0(A_17), B_19) | ~m1_subset_1(B_19, u1_struct_0(A_17)) | ~l1_orders_2(A_17) | ~v1_yellow_0(A_17) | ~v5_orders_2(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.06/1.74  tff(c_787, plain, (![D_138, B_139, A_140, C_141]: (r2_hidden(D_138, B_139) | ~r1_orders_2(A_140, C_141, D_138) | ~r2_hidden(C_141, B_139) | ~m1_subset_1(D_138, u1_struct_0(A_140)) | ~m1_subset_1(C_141, u1_struct_0(A_140)) | ~v13_waybel_0(B_139, A_140) | ~m1_subset_1(B_139, k1_zfmisc_1(u1_struct_0(A_140))) | ~l1_orders_2(A_140))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.06/1.74  tff(c_945, plain, (![B_155, B_156, A_157]: (r2_hidden(B_155, B_156) | ~r2_hidden(k3_yellow_0(A_157), B_156) | ~m1_subset_1(k3_yellow_0(A_157), u1_struct_0(A_157)) | ~v13_waybel_0(B_156, A_157) | ~m1_subset_1(B_156, k1_zfmisc_1(u1_struct_0(A_157))) | ~m1_subset_1(B_155, u1_struct_0(A_157)) | ~l1_orders_2(A_157) | ~v1_yellow_0(A_157) | ~v5_orders_2(A_157) | v2_struct_0(A_157))), inference(resolution, [status(thm)], [c_24, c_787])).
% 4.06/1.74  tff(c_948, plain, (![B_155, B_156]: (r2_hidden(B_155, B_156) | ~r2_hidden(k3_yellow_0('#skF_5'), B_156) | ~v13_waybel_0(B_156, '#skF_5') | ~m1_subset_1(B_156, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_155, u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v1_yellow_0('#skF_5') | ~v5_orders_2('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_179, c_945])).
% 4.06/1.74  tff(c_953, plain, (![B_155, B_156]: (r2_hidden(B_155, B_156) | ~r2_hidden(k3_yellow_0('#skF_5'), B_156) | ~v13_waybel_0(B_156, '#skF_5') | ~m1_subset_1(B_156, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_155, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_54, c_52, c_50, c_948])).
% 4.06/1.74  tff(c_956, plain, (![B_158, B_159]: (r2_hidden(B_158, B_159) | ~r2_hidden(k3_yellow_0('#skF_5'), B_159) | ~v13_waybel_0(B_159, '#skF_5') | ~m1_subset_1(B_159, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_158, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_60, c_953])).
% 4.06/1.74  tff(c_985, plain, (![B_158]: (r2_hidden(B_158, '#skF_6') | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v13_waybel_0('#skF_6', '#skF_5') | ~m1_subset_1(B_158, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_42, c_956])).
% 4.06/1.74  tff(c_1002, plain, (![B_160]: (r2_hidden(B_160, '#skF_6') | ~m1_subset_1(B_160, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_137, c_985])).
% 4.06/1.74  tff(c_1332, plain, (![A_169]: (r2_hidden('#skF_1'(A_169, u1_struct_0('#skF_5')), '#skF_6') | m1_subset_1('#skF_2'(A_169, u1_struct_0('#skF_5')), A_169) | u1_struct_0('#skF_5')=A_169)), inference(resolution, [status(thm)], [c_266, c_1002])).
% 4.06/1.74  tff(c_193, plain, (![A_74, B_75]: (~r2_hidden('#skF_1'(A_74, B_75), A_74) | r2_hidden('#skF_2'(A_74, B_75), A_74) | B_75=A_74)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.06/1.74  tff(c_203, plain, (![A_74, B_75]: (m1_subset_1('#skF_2'(A_74, B_75), A_74) | ~r2_hidden('#skF_1'(A_74, B_75), A_74) | B_75=A_74)), inference(resolution, [status(thm)], [c_193, c_16])).
% 4.06/1.74  tff(c_1382, plain, (m1_subset_1('#skF_2'('#skF_6', u1_struct_0('#skF_5')), '#skF_6') | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_1332, c_203])).
% 4.06/1.75  tff(c_1403, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(splitLeft, [status(thm)], [c_1382])).
% 4.06/1.75  tff(c_138, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_62])).
% 4.06/1.75  tff(c_1419, plain, (v1_subset_1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1403, c_138])).
% 4.06/1.75  tff(c_1423, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_1419])).
% 4.06/1.75  tff(c_1425, plain, (u1_struct_0('#skF_5')!='#skF_6'), inference(splitRight, [status(thm)], [c_1382])).
% 4.06/1.75  tff(c_216, plain, (![A_76, B_77]: (m1_subset_1('#skF_1'(A_76, B_77), B_77) | r2_hidden('#skF_2'(A_76, B_77), A_76) | B_77=A_76)), inference(resolution, [status(thm)], [c_204, c_16])).
% 4.06/1.75  tff(c_1081, plain, (![A_76]: (r2_hidden('#skF_1'(A_76, u1_struct_0('#skF_5')), '#skF_6') | r2_hidden('#skF_2'(A_76, u1_struct_0('#skF_5')), A_76) | u1_struct_0('#skF_5')=A_76)), inference(resolution, [status(thm)], [c_216, c_1002])).
% 4.06/1.75  tff(c_145, plain, (![B_60, A_61]: (v1_xboole_0(B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(A_61)) | ~v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.06/1.75  tff(c_148, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_42, c_145])).
% 4.06/1.75  tff(c_154, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_48, c_148])).
% 4.06/1.75  tff(c_18, plain, (![A_11, B_12]: (r2_hidden(A_11, B_12) | v1_xboole_0(B_12) | ~m1_subset_1(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.06/1.75  tff(c_187, plain, (![A_72, B_73]: (r2_hidden('#skF_1'(A_72, B_73), B_73) | ~r2_hidden('#skF_2'(A_72, B_73), B_73) | B_73=A_72)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.06/1.75  tff(c_367, plain, (![A_94, B_95]: (r2_hidden('#skF_1'(A_94, B_95), B_95) | B_95=A_94 | v1_xboole_0(B_95) | ~m1_subset_1('#skF_2'(A_94, B_95), B_95))), inference(resolution, [status(thm)], [c_18, c_187])).
% 4.06/1.75  tff(c_403, plain, (![A_100, B_101]: (m1_subset_1('#skF_1'(A_100, B_101), B_101) | B_101=A_100 | v1_xboole_0(B_101) | ~m1_subset_1('#skF_2'(A_100, B_101), B_101))), inference(resolution, [status(thm)], [c_367, c_16])).
% 4.06/1.75  tff(c_417, plain, (![A_100]: (m1_subset_1('#skF_1'(A_100, u1_struct_0('#skF_5')), u1_struct_0('#skF_5')) | u1_struct_0('#skF_5')=A_100 | v1_xboole_0(u1_struct_0('#skF_5')) | ~r2_hidden('#skF_2'(A_100, u1_struct_0('#skF_5')), '#skF_6'))), inference(resolution, [status(thm)], [c_179, c_403])).
% 4.06/1.75  tff(c_424, plain, (![A_100]: (m1_subset_1('#skF_1'(A_100, u1_struct_0('#skF_5')), u1_struct_0('#skF_5')) | u1_struct_0('#skF_5')=A_100 | ~r2_hidden('#skF_2'(A_100, u1_struct_0('#skF_5')), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_154, c_417])).
% 4.06/1.75  tff(c_1553, plain, (![A_175]: (r2_hidden('#skF_1'(A_175, u1_struct_0('#skF_5')), '#skF_6') | u1_struct_0('#skF_5')=A_175 | ~r2_hidden('#skF_2'(A_175, u1_struct_0('#skF_5')), '#skF_6'))), inference(resolution, [status(thm)], [c_424, c_1002])).
% 4.06/1.75  tff(c_1565, plain, (r2_hidden('#skF_1'('#skF_6', u1_struct_0('#skF_5')), '#skF_6') | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_1081, c_1553])).
% 4.06/1.75  tff(c_1581, plain, (r2_hidden('#skF_1'('#skF_6', u1_struct_0('#skF_5')), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_1425, c_1425, c_1565])).
% 4.06/1.75  tff(c_6, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), A_1) | r2_hidden('#skF_2'(A_1, B_2), A_1) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.06/1.75  tff(c_1602, plain, (m1_subset_1('#skF_1'('#skF_6', u1_struct_0('#skF_5')), '#skF_6')), inference(resolution, [status(thm)], [c_1581, c_16])).
% 4.06/1.75  tff(c_182, plain, (![A_70, B_71]: (~r2_hidden('#skF_1'(A_70, B_71), A_70) | ~r2_hidden('#skF_2'(A_70, B_71), B_71) | B_71=A_70)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.06/1.75  tff(c_348, plain, (![B_92, B_93]: (~r2_hidden('#skF_2'(B_92, B_93), B_93) | B_93=B_92 | v1_xboole_0(B_92) | ~m1_subset_1('#skF_1'(B_92, B_93), B_92))), inference(resolution, [status(thm)], [c_18, c_182])).
% 4.06/1.75  tff(c_366, plain, (![B_92, B_12]: (B_92=B_12 | v1_xboole_0(B_92) | ~m1_subset_1('#skF_1'(B_92, B_12), B_92) | v1_xboole_0(B_12) | ~m1_subset_1('#skF_2'(B_92, B_12), B_12))), inference(resolution, [status(thm)], [c_18, c_348])).
% 4.06/1.75  tff(c_1604, plain, (u1_struct_0('#skF_5')='#skF_6' | v1_xboole_0('#skF_6') | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_2'('#skF_6', u1_struct_0('#skF_5')), u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_1602, c_366])).
% 4.06/1.75  tff(c_1607, plain, (~m1_subset_1('#skF_2'('#skF_6', u1_struct_0('#skF_5')), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_154, c_48, c_1425, c_1604])).
% 4.06/1.75  tff(c_1611, plain, (~r2_hidden('#skF_2'('#skF_6', u1_struct_0('#skF_5')), '#skF_6')), inference(resolution, [status(thm)], [c_179, c_1607])).
% 4.06/1.75  tff(c_1619, plain, (~r2_hidden('#skF_1'('#skF_6', u1_struct_0('#skF_5')), '#skF_6') | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_6, c_1611])).
% 4.06/1.75  tff(c_1628, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1581, c_1619])).
% 4.06/1.75  tff(c_1630, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1425, c_1628])).
% 4.06/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.06/1.75  
% 4.06/1.75  Inference rules
% 4.06/1.75  ----------------------
% 4.06/1.75  #Ref     : 0
% 4.06/1.75  #Sup     : 306
% 4.06/1.75  #Fact    : 0
% 4.06/1.75  #Define  : 0
% 4.06/1.75  #Split   : 4
% 4.06/1.75  #Chain   : 0
% 4.06/1.75  #Close   : 0
% 4.06/1.75  
% 4.06/1.75  Ordering : KBO
% 4.06/1.75  
% 4.06/1.75  Simplification rules
% 4.06/1.75  ----------------------
% 4.06/1.75  #Subsume      : 28
% 4.06/1.75  #Demod        : 73
% 4.06/1.75  #Tautology    : 61
% 4.06/1.75  #SimpNegUnit  : 38
% 4.06/1.75  #BackRed      : 20
% 4.06/1.75  
% 4.06/1.75  #Partial instantiations: 0
% 4.06/1.75  #Strategies tried      : 1
% 4.06/1.75  
% 4.06/1.75  Timing (in seconds)
% 4.06/1.75  ----------------------
% 4.06/1.75  Preprocessing        : 0.31
% 4.06/1.75  Parsing              : 0.17
% 4.06/1.75  CNF conversion       : 0.03
% 4.06/1.75  Main loop            : 0.63
% 4.06/1.75  Inferencing          : 0.21
% 4.06/1.75  Reduction            : 0.17
% 4.06/1.75  Demodulation         : 0.11
% 4.06/1.75  BG Simplification    : 0.03
% 4.06/1.75  Subsumption          : 0.17
% 4.06/1.75  Abstraction          : 0.03
% 4.06/1.75  MUC search           : 0.00
% 4.06/1.75  Cooper               : 0.00
% 4.06/1.75  Total                : 0.98
% 4.06/1.75  Index Insertion      : 0.00
% 4.06/1.75  Index Deletion       : 0.00
% 4.06/1.75  Index Matching       : 0.00
% 4.06/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
