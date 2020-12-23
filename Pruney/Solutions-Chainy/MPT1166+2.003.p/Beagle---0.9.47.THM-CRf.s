%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:50 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 387 expanded)
%              Number of leaves         :   27 ( 165 expanded)
%              Depth                    :   15
%              Number of atoms          :  205 (1851 expanded)
%              Number of equality atoms :   34 ( 186 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_orders_2 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(m1_orders_2,type,(
    m1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_137,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( B != k1_xboole_0
                    & m1_orders_2(B,A,C)
                    & m1_orders_2(C,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_orders_2)).

tff(f_111,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_orders_2(C,A,B)
             => r1_tarski(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_orders_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_72,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( B != k1_xboole_0
                 => ( m1_orders_2(C,A,B)
                  <=> ? [D] :
                        ( m1_subset_1(D,u1_struct_0(A))
                        & r2_hidden(D,B)
                        & C = k3_orders_2(A,B,D) ) ) )
                & ( B = k1_xboole_0
                 => ( m1_orders_2(C,A,B)
                  <=> C = k1_xboole_0 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_orders_2)).

tff(f_92,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ~ r2_hidden(B,k3_orders_2(A,C,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_orders_2)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_42,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_40,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_38,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_36,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_28,plain,(
    m1_orders_2('#skF_3','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_65,plain,(
    ! [C_55,B_56,A_57] :
      ( r1_tarski(C_55,B_56)
      | ~ m1_orders_2(C_55,A_57,B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_orders_2(A_57)
      | ~ v5_orders_2(A_57)
      | ~ v4_orders_2(A_57)
      | ~ v3_orders_2(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_69,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_65])).

tff(c_76,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_32,c_69])).

tff(c_77,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_76])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_26,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_67,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_65])).

tff(c_72,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_34,c_67])).

tff(c_73,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_72])).

tff(c_48,plain,(
    ! [A_50,B_51] :
      ( r2_xboole_0(A_50,B_51)
      | B_51 = A_50
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( ~ r2_xboole_0(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_60,plain,(
    ! [B_51,A_50] :
      ( ~ r1_tarski(B_51,A_50)
      | B_51 = A_50
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(resolution,[status(thm)],[c_48,c_8])).

tff(c_80,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_73,c_60])).

tff(c_87,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_80])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_93,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_30])).

tff(c_92,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_28])).

tff(c_20,plain,(
    ! [A_5,B_17,C_23] :
      ( m1_subset_1('#skF_1'(A_5,B_17,C_23),u1_struct_0(A_5))
      | ~ m1_orders_2(C_23,A_5,B_17)
      | k1_xboole_0 = B_17
      | ~ m1_subset_1(C_23,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_orders_2(A_5)
      | ~ v5_orders_2(A_5)
      | ~ v4_orders_2(A_5)
      | ~ v3_orders_2(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_123,plain,(
    ! [A_63,B_64,C_65] :
      ( r2_hidden('#skF_1'(A_63,B_64,C_65),B_64)
      | ~ m1_orders_2(C_65,A_63,B_64)
      | k1_xboole_0 = B_64
      | ~ m1_subset_1(C_65,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_orders_2(A_63)
      | ~ v5_orders_2(A_63)
      | ~ v4_orders_2(A_63)
      | ~ v3_orders_2(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_125,plain,(
    ! [B_64] :
      ( r2_hidden('#skF_1'('#skF_2',B_64,'#skF_4'),B_64)
      | ~ m1_orders_2('#skF_4','#skF_2',B_64)
      | k1_xboole_0 = B_64
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_123])).

tff(c_128,plain,(
    ! [B_64] :
      ( r2_hidden('#skF_1'('#skF_2',B_64,'#skF_4'),B_64)
      | ~ m1_orders_2('#skF_4','#skF_2',B_64)
      | k1_xboole_0 = B_64
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_125])).

tff(c_130,plain,(
    ! [B_66] :
      ( r2_hidden('#skF_1'('#skF_2',B_66,'#skF_4'),B_66)
      | ~ m1_orders_2('#skF_4','#skF_2',B_66)
      | k1_xboole_0 = B_66
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_128])).

tff(c_132,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_4'),'#skF_4')
    | ~ m1_orders_2('#skF_4','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32,c_130])).

tff(c_135,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_4'),'#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_132])).

tff(c_136,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_135])).

tff(c_138,plain,(
    ! [A_70,B_71,C_72] :
      ( k3_orders_2(A_70,B_71,'#skF_1'(A_70,B_71,C_72)) = C_72
      | ~ m1_orders_2(C_72,A_70,B_71)
      | k1_xboole_0 = B_71
      | ~ m1_subset_1(C_72,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_orders_2(A_70)
      | ~ v5_orders_2(A_70)
      | ~ v4_orders_2(A_70)
      | ~ v3_orders_2(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_140,plain,(
    ! [B_71] :
      ( k3_orders_2('#skF_2',B_71,'#skF_1'('#skF_2',B_71,'#skF_4')) = '#skF_4'
      | ~ m1_orders_2('#skF_4','#skF_2',B_71)
      | k1_xboole_0 = B_71
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_138])).

tff(c_143,plain,(
    ! [B_71] :
      ( k3_orders_2('#skF_2',B_71,'#skF_1'('#skF_2',B_71,'#skF_4')) = '#skF_4'
      | ~ m1_orders_2('#skF_4','#skF_2',B_71)
      | k1_xboole_0 = B_71
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_140])).

tff(c_146,plain,(
    ! [B_76] :
      ( k3_orders_2('#skF_2',B_76,'#skF_1'('#skF_2',B_76,'#skF_4')) = '#skF_4'
      | ~ m1_orders_2('#skF_4','#skF_2',B_76)
      | k1_xboole_0 = B_76
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_143])).

tff(c_148,plain,
    ( k3_orders_2('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_4','#skF_4')) = '#skF_4'
    | ~ m1_orders_2('#skF_4','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32,c_146])).

tff(c_151,plain,
    ( k3_orders_2('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_4','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_148])).

tff(c_152,plain,(
    k3_orders_2('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_4','#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_151])).

tff(c_22,plain,(
    ! [B_31,A_27,C_33] :
      ( ~ r2_hidden(B_31,k3_orders_2(A_27,C_33,B_31))
      | ~ m1_subset_1(C_33,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ m1_subset_1(B_31,u1_struct_0(A_27))
      | ~ l1_orders_2(A_27)
      | ~ v5_orders_2(A_27)
      | ~ v4_orders_2(A_27)
      | ~ v3_orders_2(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_157,plain,
    ( ~ r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_4'),u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_22])).

tff(c_164,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_4'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_32,c_136,c_157])).

tff(c_165,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_164])).

tff(c_169,plain,
    ( ~ m1_orders_2('#skF_4','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_165])).

tff(c_172,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_32,c_92,c_169])).

tff(c_174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_93,c_172])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:21:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.27  
% 2.18/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.27  %$ m1_orders_2 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.18/1.27  
% 2.18/1.27  %Foreground sorts:
% 2.18/1.27  
% 2.18/1.27  
% 2.18/1.27  %Background operators:
% 2.18/1.27  
% 2.18/1.27  
% 2.18/1.27  %Foreground operators:
% 2.18/1.27  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.18/1.27  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.18/1.27  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.18/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.18/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.18/1.27  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 2.18/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.18/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.27  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.18/1.27  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.18/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.27  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.18/1.27  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.18/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.27  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 2.18/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.18/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.18/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.27  
% 2.18/1.29  tff(f_137, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_orders_2)).
% 2.18/1.29  tff(f_111, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_orders_2)).
% 2.18/1.29  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.18/1.29  tff(f_37, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_xboole_1)).
% 2.18/1.29  tff(f_72, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((~(B = k1_xboole_0) => (m1_orders_2(C, A, B) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(A)) & r2_hidden(D, B)) & (C = k3_orders_2(A, B, D)))))) & ((B = k1_xboole_0) => (m1_orders_2(C, A, B) <=> (C = k1_xboole_0)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d15_orders_2)).
% 2.18/1.29  tff(f_92, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~r2_hidden(B, k3_orders_2(A, C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_orders_2)).
% 2.18/1.29  tff(c_44, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.18/1.29  tff(c_42, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.18/1.29  tff(c_40, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.18/1.29  tff(c_38, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.18/1.29  tff(c_36, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.18/1.29  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.18/1.29  tff(c_28, plain, (m1_orders_2('#skF_3', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.18/1.29  tff(c_65, plain, (![C_55, B_56, A_57]: (r1_tarski(C_55, B_56) | ~m1_orders_2(C_55, A_57, B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_orders_2(A_57) | ~v5_orders_2(A_57) | ~v4_orders_2(A_57) | ~v3_orders_2(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.18/1.29  tff(c_69, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_65])).
% 2.18/1.29  tff(c_76, plain, (r1_tarski('#skF_3', '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_32, c_69])).
% 2.18/1.29  tff(c_77, plain, (r1_tarski('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_44, c_76])).
% 2.18/1.29  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.18/1.29  tff(c_26, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.18/1.29  tff(c_67, plain, (r1_tarski('#skF_4', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_65])).
% 2.18/1.29  tff(c_72, plain, (r1_tarski('#skF_4', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_34, c_67])).
% 2.18/1.29  tff(c_73, plain, (r1_tarski('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_44, c_72])).
% 2.18/1.29  tff(c_48, plain, (![A_50, B_51]: (r2_xboole_0(A_50, B_51) | B_51=A_50 | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.18/1.29  tff(c_8, plain, (![B_4, A_3]: (~r2_xboole_0(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.18/1.29  tff(c_60, plain, (![B_51, A_50]: (~r1_tarski(B_51, A_50) | B_51=A_50 | ~r1_tarski(A_50, B_51))), inference(resolution, [status(thm)], [c_48, c_8])).
% 2.18/1.29  tff(c_80, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_73, c_60])).
% 2.18/1.29  tff(c_87, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_77, c_80])).
% 2.18/1.29  tff(c_30, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.18/1.29  tff(c_93, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_87, c_30])).
% 2.18/1.29  tff(c_92, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_28])).
% 2.18/1.29  tff(c_20, plain, (![A_5, B_17, C_23]: (m1_subset_1('#skF_1'(A_5, B_17, C_23), u1_struct_0(A_5)) | ~m1_orders_2(C_23, A_5, B_17) | k1_xboole_0=B_17 | ~m1_subset_1(C_23, k1_zfmisc_1(u1_struct_0(A_5))) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_5))) | ~l1_orders_2(A_5) | ~v5_orders_2(A_5) | ~v4_orders_2(A_5) | ~v3_orders_2(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.18/1.29  tff(c_123, plain, (![A_63, B_64, C_65]: (r2_hidden('#skF_1'(A_63, B_64, C_65), B_64) | ~m1_orders_2(C_65, A_63, B_64) | k1_xboole_0=B_64 | ~m1_subset_1(C_65, k1_zfmisc_1(u1_struct_0(A_63))) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_orders_2(A_63) | ~v5_orders_2(A_63) | ~v4_orders_2(A_63) | ~v3_orders_2(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.18/1.29  tff(c_125, plain, (![B_64]: (r2_hidden('#skF_1'('#skF_2', B_64, '#skF_4'), B_64) | ~m1_orders_2('#skF_4', '#skF_2', B_64) | k1_xboole_0=B_64 | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_123])).
% 2.18/1.29  tff(c_128, plain, (![B_64]: (r2_hidden('#skF_1'('#skF_2', B_64, '#skF_4'), B_64) | ~m1_orders_2('#skF_4', '#skF_2', B_64) | k1_xboole_0=B_64 | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_125])).
% 2.18/1.29  tff(c_130, plain, (![B_66]: (r2_hidden('#skF_1'('#skF_2', B_66, '#skF_4'), B_66) | ~m1_orders_2('#skF_4', '#skF_2', B_66) | k1_xboole_0=B_66 | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_44, c_128])).
% 2.18/1.29  tff(c_132, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_4'), '#skF_4') | ~m1_orders_2('#skF_4', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_32, c_130])).
% 2.18/1.29  tff(c_135, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_4'), '#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_132])).
% 2.18/1.29  tff(c_136, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_93, c_135])).
% 2.18/1.29  tff(c_138, plain, (![A_70, B_71, C_72]: (k3_orders_2(A_70, B_71, '#skF_1'(A_70, B_71, C_72))=C_72 | ~m1_orders_2(C_72, A_70, B_71) | k1_xboole_0=B_71 | ~m1_subset_1(C_72, k1_zfmisc_1(u1_struct_0(A_70))) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_orders_2(A_70) | ~v5_orders_2(A_70) | ~v4_orders_2(A_70) | ~v3_orders_2(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.18/1.29  tff(c_140, plain, (![B_71]: (k3_orders_2('#skF_2', B_71, '#skF_1'('#skF_2', B_71, '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', B_71) | k1_xboole_0=B_71 | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_138])).
% 2.18/1.29  tff(c_143, plain, (![B_71]: (k3_orders_2('#skF_2', B_71, '#skF_1'('#skF_2', B_71, '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', B_71) | k1_xboole_0=B_71 | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_140])).
% 2.18/1.29  tff(c_146, plain, (![B_76]: (k3_orders_2('#skF_2', B_76, '#skF_1'('#skF_2', B_76, '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', B_76) | k1_xboole_0=B_76 | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_44, c_143])).
% 2.18/1.29  tff(c_148, plain, (k3_orders_2('#skF_2', '#skF_4', '#skF_1'('#skF_2', '#skF_4', '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_32, c_146])).
% 2.18/1.29  tff(c_151, plain, (k3_orders_2('#skF_2', '#skF_4', '#skF_1'('#skF_2', '#skF_4', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_148])).
% 2.18/1.29  tff(c_152, plain, (k3_orders_2('#skF_2', '#skF_4', '#skF_1'('#skF_2', '#skF_4', '#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_93, c_151])).
% 2.18/1.29  tff(c_22, plain, (![B_31, A_27, C_33]: (~r2_hidden(B_31, k3_orders_2(A_27, C_33, B_31)) | ~m1_subset_1(C_33, k1_zfmisc_1(u1_struct_0(A_27))) | ~m1_subset_1(B_31, u1_struct_0(A_27)) | ~l1_orders_2(A_27) | ~v5_orders_2(A_27) | ~v4_orders_2(A_27) | ~v3_orders_2(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.18/1.29  tff(c_157, plain, (~r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_4'), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_152, c_22])).
% 2.18/1.29  tff(c_164, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_4'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_32, c_136, c_157])).
% 2.18/1.29  tff(c_165, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_4'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_44, c_164])).
% 2.18/1.29  tff(c_169, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_20, c_165])).
% 2.18/1.29  tff(c_172, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_32, c_92, c_169])).
% 2.18/1.29  tff(c_174, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_93, c_172])).
% 2.18/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.29  
% 2.18/1.29  Inference rules
% 2.18/1.29  ----------------------
% 2.18/1.29  #Ref     : 0
% 2.18/1.29  #Sup     : 21
% 2.18/1.29  #Fact    : 0
% 2.18/1.29  #Define  : 0
% 2.18/1.29  #Split   : 1
% 2.18/1.29  #Chain   : 0
% 2.18/1.29  #Close   : 0
% 2.18/1.29  
% 2.18/1.29  Ordering : KBO
% 2.18/1.29  
% 2.18/1.29  Simplification rules
% 2.18/1.29  ----------------------
% 2.18/1.29  #Subsume      : 0
% 2.18/1.29  #Demod        : 64
% 2.18/1.29  #Tautology    : 13
% 2.18/1.29  #SimpNegUnit  : 11
% 2.18/1.29  #BackRed      : 6
% 2.18/1.29  
% 2.18/1.29  #Partial instantiations: 0
% 2.18/1.29  #Strategies tried      : 1
% 2.18/1.29  
% 2.18/1.29  Timing (in seconds)
% 2.18/1.29  ----------------------
% 2.18/1.29  Preprocessing        : 0.30
% 2.18/1.29  Parsing              : 0.15
% 2.18/1.29  CNF conversion       : 0.02
% 2.18/1.29  Main loop            : 0.17
% 2.18/1.29  Inferencing          : 0.06
% 2.18/1.29  Reduction            : 0.05
% 2.18/1.29  Demodulation         : 0.04
% 2.18/1.29  BG Simplification    : 0.01
% 2.18/1.29  Subsumption          : 0.04
% 2.18/1.29  Abstraction          : 0.01
% 2.18/1.29  MUC search           : 0.00
% 2.18/1.29  Cooper               : 0.00
% 2.18/1.30  Total                : 0.51
% 2.18/1.30  Index Insertion      : 0.00
% 2.18/1.30  Index Deletion       : 0.00
% 2.18/1.30  Index Matching       : 0.00
% 2.18/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
