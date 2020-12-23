%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:58 EST 2020

% Result     : Theorem 3.74s
% Output     : CNFRefutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 954 expanded)
%              Number of leaves         :   37 ( 345 expanded)
%              Depth                    :   15
%              Number of atoms          :  227 (4330 expanded)
%              Number of equality atoms :   29 ( 169 expanded)
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

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

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

tff(f_39,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(c_12,plain,(
    ! [A_7] : ~ v1_subset_1('#skF_3'(A_7),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14,plain,(
    ! [A_7] : m1_subset_1('#skF_3'(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_168,plain,(
    ! [B_71,A_72] :
      ( v1_subset_1(B_71,A_72)
      | B_71 = A_72
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_171,plain,(
    ! [A_7] :
      ( v1_subset_1('#skF_3'(A_7),A_7)
      | '#skF_3'(A_7) = A_7 ) ),
    inference(resolution,[status(thm)],[c_14,c_168])).

tff(c_177,plain,(
    ! [A_7] : '#skF_3'(A_7) = A_7 ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_171])).

tff(c_182,plain,(
    ! [A_7] : ~ v1_subset_1(A_7,A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_12])).

tff(c_218,plain,(
    ! [A_82,B_83] :
      ( r2_hidden('#skF_1'(A_82,B_83),B_83)
      | r2_hidden('#skF_2'(A_82,B_83),A_82)
      | B_83 = A_82 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_274,plain,(
    ! [A_90,B_91] :
      ( m1_subset_1('#skF_1'(A_90,B_91),B_91)
      | r2_hidden('#skF_2'(A_90,B_91),A_90)
      | B_91 = A_90 ) ),
    inference(resolution,[status(thm)],[c_218,c_16])).

tff(c_298,plain,(
    ! [A_90,B_91] :
      ( m1_subset_1('#skF_2'(A_90,B_91),A_90)
      | m1_subset_1('#skF_1'(A_90,B_91),B_91)
      | B_91 = A_90 ) ),
    inference(resolution,[status(thm)],[c_274,c_16])).

tff(c_44,plain,(
    v13_waybel_0('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_76,plain,(
    ! [A_54,B_55] :
      ( r2_hidden(A_54,B_55)
      | v1_xboole_0(B_55)
      | ~ m1_subset_1(A_54,B_55) ) ),
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

tff(c_75,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68])).

tff(c_79,plain,
    ( v1_xboole_0('#skF_7')
    | ~ m1_subset_1(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_76,c_75])).

tff(c_85,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_79])).

tff(c_50,plain,(
    l1_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_42,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_99,plain,(
    ! [B_59,A_60] :
      ( v1_subset_1(B_59,A_60)
      | B_59 = A_60
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_105,plain,
    ( v1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | u1_struct_0('#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_42,c_99])).

tff(c_111,plain,(
    u1_struct_0('#skF_6') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_105])).

tff(c_22,plain,(
    ! [A_16] :
      ( m1_subset_1(k3_yellow_0(A_16),u1_struct_0(A_16))
      | ~ l1_orders_2(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_135,plain,
    ( m1_subset_1(k3_yellow_0('#skF_6'),'#skF_7')
    | ~ l1_orders_2('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_22])).

tff(c_139,plain,(
    m1_subset_1(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_135])).

tff(c_141,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_139])).

tff(c_142,plain,(
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

tff(c_193,plain,(
    ! [A_75,C_76,B_77] :
      ( m1_subset_1(A_75,C_76)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(C_76))
      | ~ r2_hidden(A_75,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_196,plain,(
    ! [A_75] :
      ( m1_subset_1(A_75,u1_struct_0('#skF_6'))
      | ~ r2_hidden(A_75,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_42,c_193])).

tff(c_24,plain,(
    ! [A_17,B_19] :
      ( r1_orders_2(A_17,k3_yellow_0(A_17),B_19)
      | ~ m1_subset_1(B_19,u1_struct_0(A_17))
      | ~ l1_orders_2(A_17)
      | ~ v1_yellow_0(A_17)
      | ~ v5_orders_2(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_676,plain,(
    ! [D_137,B_138,A_139,C_140] :
      ( r2_hidden(D_137,B_138)
      | ~ r1_orders_2(A_139,C_140,D_137)
      | ~ r2_hidden(C_140,B_138)
      | ~ m1_subset_1(D_137,u1_struct_0(A_139))
      | ~ m1_subset_1(C_140,u1_struct_0(A_139))
      | ~ v13_waybel_0(B_138,A_139)
      | ~ m1_subset_1(B_138,k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ l1_orders_2(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_857,plain,(
    ! [B_154,B_155,A_156] :
      ( r2_hidden(B_154,B_155)
      | ~ r2_hidden(k3_yellow_0(A_156),B_155)
      | ~ m1_subset_1(k3_yellow_0(A_156),u1_struct_0(A_156))
      | ~ v13_waybel_0(B_155,A_156)
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ m1_subset_1(B_154,u1_struct_0(A_156))
      | ~ l1_orders_2(A_156)
      | ~ v1_yellow_0(A_156)
      | ~ v5_orders_2(A_156)
      | v2_struct_0(A_156) ) ),
    inference(resolution,[status(thm)],[c_24,c_676])).

tff(c_860,plain,(
    ! [B_154,B_155] :
      ( r2_hidden(B_154,B_155)
      | ~ r2_hidden(k3_yellow_0('#skF_6'),B_155)
      | ~ v13_waybel_0(B_155,'#skF_6')
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(B_154,u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | ~ v1_yellow_0('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ r2_hidden(k3_yellow_0('#skF_6'),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_196,c_857])).

tff(c_865,plain,(
    ! [B_154,B_155] :
      ( r2_hidden(B_154,B_155)
      | ~ r2_hidden(k3_yellow_0('#skF_6'),B_155)
      | ~ v13_waybel_0(B_155,'#skF_6')
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(B_154,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_54,c_52,c_50,c_860])).

tff(c_868,plain,(
    ! [B_157,B_158] :
      ( r2_hidden(B_157,B_158)
      | ~ r2_hidden(k3_yellow_0('#skF_6'),B_158)
      | ~ v13_waybel_0(B_158,'#skF_6')
      | ~ m1_subset_1(B_158,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(B_157,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_865])).

tff(c_894,plain,(
    ! [B_157] :
      ( r2_hidden(B_157,'#skF_7')
      | ~ r2_hidden(k3_yellow_0('#skF_6'),'#skF_7')
      | ~ v13_waybel_0('#skF_7','#skF_6')
      | ~ m1_subset_1(B_157,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_42,c_868])).

tff(c_906,plain,(
    ! [B_159] :
      ( r2_hidden(B_159,'#skF_7')
      | ~ m1_subset_1(B_159,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_142,c_894])).

tff(c_1091,plain,(
    ! [A_163] :
      ( r2_hidden('#skF_1'(A_163,u1_struct_0('#skF_6')),'#skF_7')
      | m1_subset_1('#skF_2'(A_163,u1_struct_0('#skF_6')),A_163)
      | u1_struct_0('#skF_6') = A_163 ) ),
    inference(resolution,[status(thm)],[c_298,c_906])).

tff(c_240,plain,(
    ! [A_86,B_87] :
      ( ~ r2_hidden('#skF_1'(A_86,B_87),A_86)
      | r2_hidden('#skF_2'(A_86,B_87),A_86)
      | B_87 = A_86 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_250,plain,(
    ! [A_86,B_87] :
      ( m1_subset_1('#skF_2'(A_86,B_87),A_86)
      | ~ r2_hidden('#skF_1'(A_86,B_87),A_86)
      | B_87 = A_86 ) ),
    inference(resolution,[status(thm)],[c_240,c_16])).

tff(c_1141,plain,
    ( m1_subset_1('#skF_2'('#skF_7',u1_struct_0('#skF_6')),'#skF_7')
    | u1_struct_0('#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1091,c_250])).

tff(c_1162,plain,(
    u1_struct_0('#skF_6') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_1141])).

tff(c_149,plain,(
    v1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_68])).

tff(c_1186,plain,(
    v1_subset_1('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1162,c_149])).

tff(c_1190,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_1186])).

tff(c_1192,plain,(
    u1_struct_0('#skF_6') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1141])).

tff(c_151,plain,(
    ! [B_66,A_67] :
      ( v1_xboole_0(B_66)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_67))
      | ~ v1_xboole_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_157,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_42,c_151])).

tff(c_161,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_157])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( r2_hidden(A_11,B_12)
      | v1_xboole_0(B_12)
      | ~ m1_subset_1(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_299,plain,(
    ! [A_92,B_93] :
      ( m1_subset_1('#skF_2'(A_92,B_93),A_92)
      | ~ r2_hidden('#skF_1'(A_92,B_93),A_92)
      | B_93 = A_92 ) ),
    inference(resolution,[status(thm)],[c_240,c_16])).

tff(c_312,plain,(
    ! [B_12,B_93] :
      ( m1_subset_1('#skF_2'(B_12,B_93),B_12)
      | B_93 = B_12
      | v1_xboole_0(B_12)
      | ~ m1_subset_1('#skF_1'(B_12,B_93),B_12) ) ),
    inference(resolution,[status(thm)],[c_18,c_299])).

tff(c_929,plain,(
    ! [B_93] :
      ( r2_hidden('#skF_2'(u1_struct_0('#skF_6'),B_93),'#skF_7')
      | u1_struct_0('#skF_6') = B_93
      | v1_xboole_0(u1_struct_0('#skF_6'))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_6'),B_93),u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_312,c_906])).

tff(c_981,plain,(
    ! [B_160] :
      ( r2_hidden('#skF_2'(u1_struct_0('#skF_6'),B_160),'#skF_7')
      | u1_struct_0('#skF_6') = B_160
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_6'),B_160),u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_161,c_929])).

tff(c_1193,plain,(
    ! [B_167] :
      ( r2_hidden('#skF_2'(u1_struct_0('#skF_6'),B_167),'#skF_7')
      | u1_struct_0('#skF_6') = B_167
      | ~ r2_hidden('#skF_1'(u1_struct_0('#skF_6'),B_167),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_196,c_981])).

tff(c_213,plain,(
    ! [A_80,B_81] :
      ( ~ r2_hidden('#skF_1'(A_80,B_81),A_80)
      | ~ r2_hidden('#skF_2'(A_80,B_81),B_81)
      | B_81 = A_80 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_217,plain,(
    ! [B_12,B_81] :
      ( ~ r2_hidden('#skF_2'(B_12,B_81),B_81)
      | B_81 = B_12
      | v1_xboole_0(B_12)
      | ~ m1_subset_1('#skF_1'(B_12,B_81),B_12) ) ),
    inference(resolution,[status(thm)],[c_18,c_213])).

tff(c_1196,plain,
    ( v1_xboole_0(u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_6'),'#skF_7'),u1_struct_0('#skF_6'))
    | u1_struct_0('#skF_6') = '#skF_7'
    | ~ r2_hidden('#skF_1'(u1_struct_0('#skF_6'),'#skF_7'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_1193,c_217])).

tff(c_1206,plain,
    ( ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_6'),'#skF_7'),u1_struct_0('#skF_6'))
    | ~ r2_hidden('#skF_1'(u1_struct_0('#skF_6'),'#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_1192,c_161,c_1192,c_1196])).

tff(c_1211,plain,(
    ~ r2_hidden('#skF_1'(u1_struct_0('#skF_6'),'#skF_7'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1206])).

tff(c_227,plain,(
    ! [A_82,B_83] :
      ( m1_subset_1('#skF_2'(A_82,B_83),A_82)
      | r2_hidden('#skF_1'(A_82,B_83),B_83)
      | B_83 = A_82 ) ),
    inference(resolution,[status(thm)],[c_218,c_16])).

tff(c_1228,plain,(
    ! [B_168] :
      ( r2_hidden('#skF_2'(u1_struct_0('#skF_6'),B_168),'#skF_7')
      | r2_hidden('#skF_1'(u1_struct_0('#skF_6'),B_168),B_168)
      | u1_struct_0('#skF_6') = B_168 ) ),
    inference(resolution,[status(thm)],[c_227,c_906])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2),B_2)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1235,plain,
    ( r2_hidden('#skF_1'(u1_struct_0('#skF_6'),'#skF_7'),'#skF_7')
    | u1_struct_0('#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1228,c_4])).

tff(c_1268,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1192,c_1211,c_1192,c_1211,c_1235])).

tff(c_1270,plain,(
    r2_hidden('#skF_1'(u1_struct_0('#skF_6'),'#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_1206])).

tff(c_1269,plain,(
    ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_6'),'#skF_7'),u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1206])).

tff(c_1287,plain,(
    ~ r2_hidden('#skF_1'(u1_struct_0('#skF_6'),'#skF_7'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_196,c_1269])).

tff(c_1291,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1270,c_1287])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:40:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.74/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/1.65  
% 3.74/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/1.65  %$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > #skF_7 > #skF_6 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 3.74/1.65  
% 3.74/1.65  %Foreground sorts:
% 3.74/1.65  
% 3.74/1.65  
% 3.74/1.65  %Background operators:
% 3.74/1.65  
% 3.74/1.65  
% 3.74/1.65  %Foreground operators:
% 3.74/1.65  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.74/1.65  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.74/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.74/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.74/1.65  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.74/1.65  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.74/1.65  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 3.74/1.65  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 3.74/1.65  tff('#skF_7', type, '#skF_7': $i).
% 3.74/1.65  tff('#skF_6', type, '#skF_6': $i).
% 3.74/1.65  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.74/1.65  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.74/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.74/1.65  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.74/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.74/1.65  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.74/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.74/1.65  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.74/1.65  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 3.74/1.65  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.74/1.65  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.74/1.65  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.74/1.65  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.74/1.65  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.74/1.65  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 3.74/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.74/1.65  
% 3.74/1.67  tff(f_45, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_subset_1)).
% 3.74/1.67  tff(f_105, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 3.74/1.67  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 3.74/1.67  tff(f_49, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.74/1.67  tff(f_134, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_subset_1(B, u1_struct_0(A)) <=> ~r2_hidden(k3_yellow_0(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_7)).
% 3.74/1.67  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.74/1.67  tff(f_65, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(k3_yellow_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow_0)).
% 3.74/1.67  tff(f_61, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.74/1.67  tff(f_79, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, k3_yellow_0(A), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_yellow_0)).
% 3.74/1.67  tff(f_98, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v13_waybel_0(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r1_orders_2(A, C, D)) => r2_hidden(D, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_waybel_0)).
% 3.74/1.67  tff(f_39, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.74/1.67  tff(c_12, plain, (![A_7]: (~v1_subset_1('#skF_3'(A_7), A_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.74/1.67  tff(c_14, plain, (![A_7]: (m1_subset_1('#skF_3'(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.74/1.67  tff(c_168, plain, (![B_71, A_72]: (v1_subset_1(B_71, A_72) | B_71=A_72 | ~m1_subset_1(B_71, k1_zfmisc_1(A_72)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.74/1.67  tff(c_171, plain, (![A_7]: (v1_subset_1('#skF_3'(A_7), A_7) | '#skF_3'(A_7)=A_7)), inference(resolution, [status(thm)], [c_14, c_168])).
% 3.74/1.67  tff(c_177, plain, (![A_7]: ('#skF_3'(A_7)=A_7)), inference(negUnitSimplification, [status(thm)], [c_12, c_171])).
% 3.74/1.67  tff(c_182, plain, (![A_7]: (~v1_subset_1(A_7, A_7))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_12])).
% 3.74/1.67  tff(c_218, plain, (![A_82, B_83]: (r2_hidden('#skF_1'(A_82, B_83), B_83) | r2_hidden('#skF_2'(A_82, B_83), A_82) | B_83=A_82)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.74/1.67  tff(c_16, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.74/1.67  tff(c_274, plain, (![A_90, B_91]: (m1_subset_1('#skF_1'(A_90, B_91), B_91) | r2_hidden('#skF_2'(A_90, B_91), A_90) | B_91=A_90)), inference(resolution, [status(thm)], [c_218, c_16])).
% 3.74/1.67  tff(c_298, plain, (![A_90, B_91]: (m1_subset_1('#skF_2'(A_90, B_91), A_90) | m1_subset_1('#skF_1'(A_90, B_91), B_91) | B_91=A_90)), inference(resolution, [status(thm)], [c_274, c_16])).
% 3.74/1.67  tff(c_44, plain, (v13_waybel_0('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.74/1.67  tff(c_48, plain, (~v1_xboole_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.74/1.67  tff(c_76, plain, (![A_54, B_55]: (r2_hidden(A_54, B_55) | v1_xboole_0(B_55) | ~m1_subset_1(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.74/1.67  tff(c_62, plain, (r2_hidden(k3_yellow_0('#skF_6'), '#skF_7') | ~v1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.74/1.67  tff(c_74, plain, (~v1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_62])).
% 3.74/1.67  tff(c_68, plain, (v1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~r2_hidden(k3_yellow_0('#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.74/1.67  tff(c_75, plain, (~r2_hidden(k3_yellow_0('#skF_6'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_74, c_68])).
% 3.74/1.67  tff(c_79, plain, (v1_xboole_0('#skF_7') | ~m1_subset_1(k3_yellow_0('#skF_6'), '#skF_7')), inference(resolution, [status(thm)], [c_76, c_75])).
% 3.74/1.67  tff(c_85, plain, (~m1_subset_1(k3_yellow_0('#skF_6'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_48, c_79])).
% 3.74/1.67  tff(c_50, plain, (l1_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.74/1.67  tff(c_42, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.74/1.67  tff(c_99, plain, (![B_59, A_60]: (v1_subset_1(B_59, A_60) | B_59=A_60 | ~m1_subset_1(B_59, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.74/1.67  tff(c_105, plain, (v1_subset_1('#skF_7', u1_struct_0('#skF_6')) | u1_struct_0('#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_42, c_99])).
% 3.74/1.67  tff(c_111, plain, (u1_struct_0('#skF_6')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_74, c_105])).
% 3.74/1.67  tff(c_22, plain, (![A_16]: (m1_subset_1(k3_yellow_0(A_16), u1_struct_0(A_16)) | ~l1_orders_2(A_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.74/1.67  tff(c_135, plain, (m1_subset_1(k3_yellow_0('#skF_6'), '#skF_7') | ~l1_orders_2('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_111, c_22])).
% 3.74/1.67  tff(c_139, plain, (m1_subset_1(k3_yellow_0('#skF_6'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_135])).
% 3.74/1.67  tff(c_141, plain, $false, inference(negUnitSimplification, [status(thm)], [c_85, c_139])).
% 3.74/1.67  tff(c_142, plain, (r2_hidden(k3_yellow_0('#skF_6'), '#skF_7')), inference(splitRight, [status(thm)], [c_62])).
% 3.74/1.67  tff(c_60, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.74/1.67  tff(c_54, plain, (v5_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.74/1.67  tff(c_52, plain, (v1_yellow_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.74/1.67  tff(c_193, plain, (![A_75, C_76, B_77]: (m1_subset_1(A_75, C_76) | ~m1_subset_1(B_77, k1_zfmisc_1(C_76)) | ~r2_hidden(A_75, B_77))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.74/1.67  tff(c_196, plain, (![A_75]: (m1_subset_1(A_75, u1_struct_0('#skF_6')) | ~r2_hidden(A_75, '#skF_7'))), inference(resolution, [status(thm)], [c_42, c_193])).
% 3.74/1.67  tff(c_24, plain, (![A_17, B_19]: (r1_orders_2(A_17, k3_yellow_0(A_17), B_19) | ~m1_subset_1(B_19, u1_struct_0(A_17)) | ~l1_orders_2(A_17) | ~v1_yellow_0(A_17) | ~v5_orders_2(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.74/1.67  tff(c_676, plain, (![D_137, B_138, A_139, C_140]: (r2_hidden(D_137, B_138) | ~r1_orders_2(A_139, C_140, D_137) | ~r2_hidden(C_140, B_138) | ~m1_subset_1(D_137, u1_struct_0(A_139)) | ~m1_subset_1(C_140, u1_struct_0(A_139)) | ~v13_waybel_0(B_138, A_139) | ~m1_subset_1(B_138, k1_zfmisc_1(u1_struct_0(A_139))) | ~l1_orders_2(A_139))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.74/1.67  tff(c_857, plain, (![B_154, B_155, A_156]: (r2_hidden(B_154, B_155) | ~r2_hidden(k3_yellow_0(A_156), B_155) | ~m1_subset_1(k3_yellow_0(A_156), u1_struct_0(A_156)) | ~v13_waybel_0(B_155, A_156) | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0(A_156))) | ~m1_subset_1(B_154, u1_struct_0(A_156)) | ~l1_orders_2(A_156) | ~v1_yellow_0(A_156) | ~v5_orders_2(A_156) | v2_struct_0(A_156))), inference(resolution, [status(thm)], [c_24, c_676])).
% 3.74/1.67  tff(c_860, plain, (![B_154, B_155]: (r2_hidden(B_154, B_155) | ~r2_hidden(k3_yellow_0('#skF_6'), B_155) | ~v13_waybel_0(B_155, '#skF_6') | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1(B_154, u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v1_yellow_0('#skF_6') | ~v5_orders_2('#skF_6') | v2_struct_0('#skF_6') | ~r2_hidden(k3_yellow_0('#skF_6'), '#skF_7'))), inference(resolution, [status(thm)], [c_196, c_857])).
% 3.74/1.67  tff(c_865, plain, (![B_154, B_155]: (r2_hidden(B_154, B_155) | ~r2_hidden(k3_yellow_0('#skF_6'), B_155) | ~v13_waybel_0(B_155, '#skF_6') | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1(B_154, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_54, c_52, c_50, c_860])).
% 3.74/1.67  tff(c_868, plain, (![B_157, B_158]: (r2_hidden(B_157, B_158) | ~r2_hidden(k3_yellow_0('#skF_6'), B_158) | ~v13_waybel_0(B_158, '#skF_6') | ~m1_subset_1(B_158, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1(B_157, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_60, c_865])).
% 3.74/1.67  tff(c_894, plain, (![B_157]: (r2_hidden(B_157, '#skF_7') | ~r2_hidden(k3_yellow_0('#skF_6'), '#skF_7') | ~v13_waybel_0('#skF_7', '#skF_6') | ~m1_subset_1(B_157, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_42, c_868])).
% 3.74/1.67  tff(c_906, plain, (![B_159]: (r2_hidden(B_159, '#skF_7') | ~m1_subset_1(B_159, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_142, c_894])).
% 3.74/1.67  tff(c_1091, plain, (![A_163]: (r2_hidden('#skF_1'(A_163, u1_struct_0('#skF_6')), '#skF_7') | m1_subset_1('#skF_2'(A_163, u1_struct_0('#skF_6')), A_163) | u1_struct_0('#skF_6')=A_163)), inference(resolution, [status(thm)], [c_298, c_906])).
% 3.74/1.67  tff(c_240, plain, (![A_86, B_87]: (~r2_hidden('#skF_1'(A_86, B_87), A_86) | r2_hidden('#skF_2'(A_86, B_87), A_86) | B_87=A_86)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.74/1.67  tff(c_250, plain, (![A_86, B_87]: (m1_subset_1('#skF_2'(A_86, B_87), A_86) | ~r2_hidden('#skF_1'(A_86, B_87), A_86) | B_87=A_86)), inference(resolution, [status(thm)], [c_240, c_16])).
% 3.74/1.67  tff(c_1141, plain, (m1_subset_1('#skF_2'('#skF_7', u1_struct_0('#skF_6')), '#skF_7') | u1_struct_0('#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_1091, c_250])).
% 3.74/1.67  tff(c_1162, plain, (u1_struct_0('#skF_6')='#skF_7'), inference(splitLeft, [status(thm)], [c_1141])).
% 3.74/1.67  tff(c_149, plain, (v1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_68])).
% 3.74/1.67  tff(c_1186, plain, (v1_subset_1('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1162, c_149])).
% 3.74/1.67  tff(c_1190, plain, $false, inference(negUnitSimplification, [status(thm)], [c_182, c_1186])).
% 3.74/1.67  tff(c_1192, plain, (u1_struct_0('#skF_6')!='#skF_7'), inference(splitRight, [status(thm)], [c_1141])).
% 3.74/1.67  tff(c_151, plain, (![B_66, A_67]: (v1_xboole_0(B_66) | ~m1_subset_1(B_66, k1_zfmisc_1(A_67)) | ~v1_xboole_0(A_67))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.74/1.67  tff(c_157, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0(u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_42, c_151])).
% 3.74/1.67  tff(c_161, plain, (~v1_xboole_0(u1_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_48, c_157])).
% 3.74/1.67  tff(c_18, plain, (![A_11, B_12]: (r2_hidden(A_11, B_12) | v1_xboole_0(B_12) | ~m1_subset_1(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.74/1.67  tff(c_299, plain, (![A_92, B_93]: (m1_subset_1('#skF_2'(A_92, B_93), A_92) | ~r2_hidden('#skF_1'(A_92, B_93), A_92) | B_93=A_92)), inference(resolution, [status(thm)], [c_240, c_16])).
% 3.74/1.67  tff(c_312, plain, (![B_12, B_93]: (m1_subset_1('#skF_2'(B_12, B_93), B_12) | B_93=B_12 | v1_xboole_0(B_12) | ~m1_subset_1('#skF_1'(B_12, B_93), B_12))), inference(resolution, [status(thm)], [c_18, c_299])).
% 3.74/1.67  tff(c_929, plain, (![B_93]: (r2_hidden('#skF_2'(u1_struct_0('#skF_6'), B_93), '#skF_7') | u1_struct_0('#skF_6')=B_93 | v1_xboole_0(u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_6'), B_93), u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_312, c_906])).
% 3.74/1.67  tff(c_981, plain, (![B_160]: (r2_hidden('#skF_2'(u1_struct_0('#skF_6'), B_160), '#skF_7') | u1_struct_0('#skF_6')=B_160 | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_6'), B_160), u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_161, c_929])).
% 3.74/1.67  tff(c_1193, plain, (![B_167]: (r2_hidden('#skF_2'(u1_struct_0('#skF_6'), B_167), '#skF_7') | u1_struct_0('#skF_6')=B_167 | ~r2_hidden('#skF_1'(u1_struct_0('#skF_6'), B_167), '#skF_7'))), inference(resolution, [status(thm)], [c_196, c_981])).
% 3.74/1.67  tff(c_213, plain, (![A_80, B_81]: (~r2_hidden('#skF_1'(A_80, B_81), A_80) | ~r2_hidden('#skF_2'(A_80, B_81), B_81) | B_81=A_80)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.74/1.67  tff(c_217, plain, (![B_12, B_81]: (~r2_hidden('#skF_2'(B_12, B_81), B_81) | B_81=B_12 | v1_xboole_0(B_12) | ~m1_subset_1('#skF_1'(B_12, B_81), B_12))), inference(resolution, [status(thm)], [c_18, c_213])).
% 3.74/1.67  tff(c_1196, plain, (v1_xboole_0(u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_6'), '#skF_7'), u1_struct_0('#skF_6')) | u1_struct_0('#skF_6')='#skF_7' | ~r2_hidden('#skF_1'(u1_struct_0('#skF_6'), '#skF_7'), '#skF_7')), inference(resolution, [status(thm)], [c_1193, c_217])).
% 3.74/1.67  tff(c_1206, plain, (~m1_subset_1('#skF_1'(u1_struct_0('#skF_6'), '#skF_7'), u1_struct_0('#skF_6')) | ~r2_hidden('#skF_1'(u1_struct_0('#skF_6'), '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_1192, c_161, c_1192, c_1196])).
% 3.74/1.67  tff(c_1211, plain, (~r2_hidden('#skF_1'(u1_struct_0('#skF_6'), '#skF_7'), '#skF_7')), inference(splitLeft, [status(thm)], [c_1206])).
% 3.74/1.67  tff(c_227, plain, (![A_82, B_83]: (m1_subset_1('#skF_2'(A_82, B_83), A_82) | r2_hidden('#skF_1'(A_82, B_83), B_83) | B_83=A_82)), inference(resolution, [status(thm)], [c_218, c_16])).
% 3.74/1.67  tff(c_1228, plain, (![B_168]: (r2_hidden('#skF_2'(u1_struct_0('#skF_6'), B_168), '#skF_7') | r2_hidden('#skF_1'(u1_struct_0('#skF_6'), B_168), B_168) | u1_struct_0('#skF_6')=B_168)), inference(resolution, [status(thm)], [c_227, c_906])).
% 3.74/1.67  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | ~r2_hidden('#skF_2'(A_1, B_2), B_2) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.74/1.67  tff(c_1235, plain, (r2_hidden('#skF_1'(u1_struct_0('#skF_6'), '#skF_7'), '#skF_7') | u1_struct_0('#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_1228, c_4])).
% 3.74/1.67  tff(c_1268, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1192, c_1211, c_1192, c_1211, c_1235])).
% 3.74/1.67  tff(c_1270, plain, (r2_hidden('#skF_1'(u1_struct_0('#skF_6'), '#skF_7'), '#skF_7')), inference(splitRight, [status(thm)], [c_1206])).
% 3.74/1.67  tff(c_1269, plain, (~m1_subset_1('#skF_1'(u1_struct_0('#skF_6'), '#skF_7'), u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_1206])).
% 3.74/1.67  tff(c_1287, plain, (~r2_hidden('#skF_1'(u1_struct_0('#skF_6'), '#skF_7'), '#skF_7')), inference(resolution, [status(thm)], [c_196, c_1269])).
% 3.74/1.67  tff(c_1291, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1270, c_1287])).
% 3.74/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/1.67  
% 3.74/1.67  Inference rules
% 3.74/1.67  ----------------------
% 3.74/1.67  #Ref     : 0
% 3.74/1.67  #Sup     : 235
% 3.74/1.67  #Fact    : 0
% 3.74/1.67  #Define  : 0
% 3.74/1.67  #Split   : 5
% 3.74/1.67  #Chain   : 0
% 3.74/1.67  #Close   : 0
% 3.74/1.67  
% 3.74/1.67  Ordering : KBO
% 3.74/1.67  
% 3.74/1.67  Simplification rules
% 3.74/1.67  ----------------------
% 3.74/1.67  #Subsume      : 18
% 3.74/1.67  #Demod        : 64
% 3.74/1.67  #Tautology    : 49
% 3.74/1.67  #SimpNegUnit  : 30
% 3.74/1.67  #BackRed      : 22
% 3.74/1.67  
% 3.74/1.67  #Partial instantiations: 0
% 3.74/1.67  #Strategies tried      : 1
% 3.74/1.67  
% 3.74/1.67  Timing (in seconds)
% 3.74/1.67  ----------------------
% 3.74/1.67  Preprocessing        : 0.34
% 3.74/1.67  Parsing              : 0.19
% 3.74/1.67  CNF conversion       : 0.03
% 3.74/1.67  Main loop            : 0.51
% 3.74/1.68  Inferencing          : 0.19
% 3.74/1.68  Reduction            : 0.14
% 3.74/1.68  Demodulation         : 0.09
% 3.74/1.68  BG Simplification    : 0.03
% 3.74/1.68  Subsumption          : 0.12
% 3.74/1.68  Abstraction          : 0.03
% 3.74/1.68  MUC search           : 0.00
% 3.74/1.68  Cooper               : 0.00
% 3.74/1.68  Total                : 0.89
% 3.74/1.68  Index Insertion      : 0.00
% 3.74/1.68  Index Deletion       : 0.00
% 3.74/1.68  Index Matching       : 0.00
% 3.74/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
