%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1959+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:43 EST 2020

% Result     : Theorem 3.78s
% Output     : CNFRefutation 4.19s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 643 expanded)
%              Number of leaves         :   35 ( 236 expanded)
%              Depth                    :   17
%              Number of atoms          :  229 (3016 expanded)
%              Number of equality atoms :   30 ( 104 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(v1_yellow_0,type,(
    v1_yellow_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_71,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_127,negated_conjecture,(
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

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(k3_yellow_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_85,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,k3_yellow_0(A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_yellow_0)).

tff(f_43,axiom,(
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

tff(f_98,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_141,plain,(
    ! [A_70,B_71] :
      ( r2_hidden('#skF_3'(A_70,B_71),B_71)
      | r2_hidden('#skF_4'(A_70,B_71),A_70)
      | B_71 = A_70 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_20,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(A_29,B_30)
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_154,plain,(
    ! [A_70,B_71] :
      ( m1_subset_1('#skF_3'(A_70,B_71),B_71)
      | r2_hidden('#skF_4'(A_70,B_71),A_70)
      | B_71 = A_70 ) ),
    inference(resolution,[status(thm)],[c_141,c_20])).

tff(c_40,plain,(
    v13_waybel_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_22,plain,(
    ! [A_31,B_32] :
      ( r2_hidden(A_31,B_32)
      | v1_xboole_0(B_32)
      | ~ m1_subset_1(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_58,plain,
    ( r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
    | ~ v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_68,plain,(
    ~ v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_64,plain,
    ( v1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_74,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_64])).

tff(c_77,plain,
    ( v1_xboole_0('#skF_6')
    | ~ m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_22,c_74])).

tff(c_80,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_77])).

tff(c_46,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_38,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_86,plain,(
    ! [B_55,A_56] :
      ( v1_subset_1(B_55,A_56)
      | B_55 = A_56
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_89,plain,
    ( v1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_38,c_86])).

tff(c_92,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_89])).

tff(c_18,plain,(
    ! [A_28] :
      ( m1_subset_1(k3_yellow_0(A_28),u1_struct_0(A_28))
      | ~ l1_orders_2(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_99,plain,
    ( m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6')
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_18])).

tff(c_103,plain,(
    m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_99])).

tff(c_105,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_103])).

tff(c_106,plain,(
    r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_50,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_48,plain,(
    v1_yellow_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_130,plain,(
    ! [A_64,C_65,B_66] :
      ( m1_subset_1(A_64,C_65)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(C_65))
      | ~ r2_hidden(A_64,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_133,plain,(
    ! [A_64] :
      ( m1_subset_1(A_64,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_64,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_38,c_130])).

tff(c_32,plain,(
    ! [A_36,B_38] :
      ( r1_orders_2(A_36,k3_yellow_0(A_36),B_38)
      | ~ m1_subset_1(B_38,u1_struct_0(A_36))
      | ~ l1_orders_2(A_36)
      | ~ v1_yellow_0(A_36)
      | ~ v5_orders_2(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_662,plain,(
    ! [D_134,B_135,A_136,C_137] :
      ( r2_hidden(D_134,B_135)
      | ~ r1_orders_2(A_136,C_137,D_134)
      | ~ r2_hidden(C_137,B_135)
      | ~ m1_subset_1(D_134,u1_struct_0(A_136))
      | ~ m1_subset_1(C_137,u1_struct_0(A_136))
      | ~ v13_waybel_0(B_135,A_136)
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ l1_orders_2(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_913,plain,(
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
    inference(resolution,[status(thm)],[c_32,c_662])).

tff(c_916,plain,(
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
    inference(resolution,[status(thm)],[c_133,c_913])).

tff(c_921,plain,(
    ! [B_155,B_156] :
      ( r2_hidden(B_155,B_156)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_156)
      | ~ v13_waybel_0(B_156,'#skF_5')
      | ~ m1_subset_1(B_156,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_155,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_50,c_48,c_46,c_916])).

tff(c_924,plain,(
    ! [B_158,B_159] :
      ( r2_hidden(B_158,B_159)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_159)
      | ~ v13_waybel_0(B_159,'#skF_5')
      | ~ m1_subset_1(B_159,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_158,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_921])).

tff(c_947,plain,(
    ! [B_158] :
      ( r2_hidden(B_158,'#skF_6')
      | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
      | ~ v13_waybel_0('#skF_6','#skF_5')
      | ~ m1_subset_1(B_158,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_38,c_924])).

tff(c_958,plain,(
    ! [B_160] :
      ( r2_hidden(B_160,'#skF_6')
      | ~ m1_subset_1(B_160,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_106,c_947])).

tff(c_1182,plain,(
    ! [A_166] :
      ( r2_hidden('#skF_3'(A_166,u1_struct_0('#skF_5')),'#skF_6')
      | r2_hidden('#skF_4'(A_166,u1_struct_0('#skF_5')),A_166)
      | u1_struct_0('#skF_5') = A_166 ) ),
    inference(resolution,[status(thm)],[c_154,c_958])).

tff(c_28,plain,(
    ! [A_33,B_34] :
      ( ~ r2_hidden('#skF_3'(A_33,B_34),A_33)
      | r2_hidden('#skF_4'(A_33,B_34),A_33)
      | B_34 = A_33 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1231,plain,
    ( r2_hidden('#skF_4'('#skF_6',u1_struct_0('#skF_5')),'#skF_6')
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1182,c_28])).

tff(c_1247,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1231])).

tff(c_107,plain,(
    v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1259,plain,(
    v1_subset_1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1247,c_107])).

tff(c_1260,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1247,c_38])).

tff(c_16,plain,(
    ! [B_27] :
      ( ~ v1_subset_1(B_27,B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1310,plain,(
    ~ v1_subset_1('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_1260,c_16])).

tff(c_1319,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1259,c_1310])).

tff(c_1321,plain,(
    u1_struct_0('#skF_5') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1231])).

tff(c_155,plain,(
    ! [A_70,B_71] :
      ( m1_subset_1('#skF_4'(A_70,B_71),A_70)
      | r2_hidden('#skF_3'(A_70,B_71),B_71)
      | B_71 = A_70 ) ),
    inference(resolution,[status(thm)],[c_141,c_20])).

tff(c_1019,plain,(
    ! [B_71] :
      ( r2_hidden('#skF_4'(u1_struct_0('#skF_5'),B_71),'#skF_6')
      | r2_hidden('#skF_3'(u1_struct_0('#skF_5'),B_71),B_71)
      | u1_struct_0('#skF_5') = B_71 ) ),
    inference(resolution,[status(thm)],[c_155,c_958])).

tff(c_119,plain,(
    ! [C_59,B_60,A_61] :
      ( ~ v1_xboole_0(C_59)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(C_59))
      | ~ r2_hidden(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_122,plain,(
    ! [A_61] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_61,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_38,c_119])).

tff(c_123,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_135,plain,(
    ! [A_68,B_69] :
      ( ~ r2_hidden('#skF_3'(A_68,B_69),A_68)
      | r2_hidden('#skF_4'(A_68,B_69),A_68)
      | B_69 = A_68 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_307,plain,(
    ! [B_90,B_91] :
      ( r2_hidden('#skF_4'(B_90,B_91),B_90)
      | B_91 = B_90
      | v1_xboole_0(B_90)
      | ~ m1_subset_1('#skF_3'(B_90,B_91),B_90) ) ),
    inference(resolution,[status(thm)],[c_22,c_135])).

tff(c_341,plain,(
    ! [B_94,B_95] :
      ( m1_subset_1('#skF_4'(B_94,B_95),B_94)
      | B_95 = B_94
      | v1_xboole_0(B_94)
      | ~ m1_subset_1('#skF_3'(B_94,B_95),B_94) ) ),
    inference(resolution,[status(thm)],[c_307,c_20])).

tff(c_355,plain,(
    ! [B_95] :
      ( m1_subset_1('#skF_4'(u1_struct_0('#skF_5'),B_95),u1_struct_0('#skF_5'))
      | u1_struct_0('#skF_5') = B_95
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_3'(u1_struct_0('#skF_5'),B_95),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_133,c_341])).

tff(c_362,plain,(
    ! [B_95] :
      ( m1_subset_1('#skF_4'(u1_struct_0('#skF_5'),B_95),u1_struct_0('#skF_5'))
      | u1_struct_0('#skF_5') = B_95
      | ~ r2_hidden('#skF_3'(u1_struct_0('#skF_5'),B_95),'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_355])).

tff(c_1474,plain,(
    ! [B_177] :
      ( r2_hidden('#skF_4'(u1_struct_0('#skF_5'),B_177),'#skF_6')
      | u1_struct_0('#skF_5') = B_177
      | ~ r2_hidden('#skF_3'(u1_struct_0('#skF_5'),B_177),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_362,c_958])).

tff(c_1478,plain,
    ( r2_hidden('#skF_4'(u1_struct_0('#skF_5'),'#skF_6'),'#skF_6')
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1019,c_1474])).

tff(c_1496,plain,(
    r2_hidden('#skF_4'(u1_struct_0('#skF_5'),'#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_1321,c_1321,c_1478])).

tff(c_26,plain,(
    ! [A_33,B_34] :
      ( r2_hidden('#skF_3'(A_33,B_34),B_34)
      | ~ r2_hidden('#skF_4'(A_33,B_34),B_34)
      | B_34 = A_33 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1517,plain,(
    m1_subset_1('#skF_4'(u1_struct_0('#skF_5'),'#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_1496,c_20])).

tff(c_167,plain,(
    ! [A_74,B_75] :
      ( ~ r2_hidden('#skF_3'(A_74,B_75),A_74)
      | ~ r2_hidden('#skF_4'(A_74,B_75),B_75)
      | B_75 = A_74 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_291,plain,(
    ! [B_86,B_87] :
      ( ~ r2_hidden('#skF_4'(B_86,B_87),B_87)
      | B_87 = B_86
      | v1_xboole_0(B_86)
      | ~ m1_subset_1('#skF_3'(B_86,B_87),B_86) ) ),
    inference(resolution,[status(thm)],[c_22,c_167])).

tff(c_366,plain,(
    ! [B_102,B_101] :
      ( B_102 = B_101
      | v1_xboole_0(B_101)
      | ~ m1_subset_1('#skF_3'(B_101,B_102),B_101)
      | v1_xboole_0(B_102)
      | ~ m1_subset_1('#skF_4'(B_101,B_102),B_102) ) ),
    inference(resolution,[status(thm)],[c_22,c_291])).

tff(c_376,plain,(
    ! [B_102] :
      ( u1_struct_0('#skF_5') = B_102
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | v1_xboole_0(B_102)
      | ~ m1_subset_1('#skF_4'(u1_struct_0('#skF_5'),B_102),B_102)
      | ~ r2_hidden('#skF_3'(u1_struct_0('#skF_5'),B_102),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_133,c_366])).

tff(c_383,plain,(
    ! [B_102] :
      ( u1_struct_0('#skF_5') = B_102
      | v1_xboole_0(B_102)
      | ~ m1_subset_1('#skF_4'(u1_struct_0('#skF_5'),B_102),B_102)
      | ~ r2_hidden('#skF_3'(u1_struct_0('#skF_5'),B_102),'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_376])).

tff(c_1539,plain,
    ( u1_struct_0('#skF_5') = '#skF_6'
    | v1_xboole_0('#skF_6')
    | ~ r2_hidden('#skF_3'(u1_struct_0('#skF_5'),'#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_1517,c_383])).

tff(c_1542,plain,(
    ~ r2_hidden('#skF_3'(u1_struct_0('#skF_5'),'#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1321,c_1539])).

tff(c_1549,plain,
    ( ~ r2_hidden('#skF_4'(u1_struct_0('#skF_5'),'#skF_6'),'#skF_6')
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_26,c_1542])).

tff(c_1559,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1496,c_1549])).

tff(c_1561,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1321,c_1559])).

tff(c_1562,plain,(
    ! [A_61] : ~ r2_hidden(A_61,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_1565,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1562,c_106])).

%------------------------------------------------------------------------------
