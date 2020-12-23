%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:48 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 3.95s
% Verified   : 
% Statistics : Number of formulae       :  198 (2911 expanded)
%              Number of leaves         :   27 (1140 expanded)
%              Depth                    :   26
%              Number of atoms          :  682 (14256 expanded)
%              Number of equality atoms :  114 ( 822 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > m1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(m1_orders_2,type,(
    m1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_138,negated_conjecture,(
    ~ ! [A] :
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

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ! [C] :
          ( m1_orders_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_orders_2)).

tff(f_74,axiom,(
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

tff(f_118,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ( r2_hidden(B,k3_orders_2(A,D,C))
                  <=> ( r2_orders_2(A,B,C)
                      & r2_hidden(B,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_45,plain,(
    ! [A_59,B_60,C_61] :
      ( r2_hidden('#skF_1'(A_59,B_60,C_61),B_60)
      | r1_tarski(B_60,C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(A_59))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [A_1,B_2,C_6] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_6),C_6)
      | r1_tarski(B_2,C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_51,plain,(
    ! [B_62,A_63] :
      ( r1_tarski(B_62,B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_63)) ) ),
    inference(resolution,[status(thm)],[c_45,c_2])).

tff(c_58,plain,(
    r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_51])).

tff(c_28,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_40,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_38,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_36,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_34,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_30,plain,(
    m1_orders_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_60,plain,(
    ! [C_65,A_66,B_67] :
      ( m1_subset_1(C_65,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ m1_orders_2(C_65,A_66,B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_orders_2(A_66)
      | ~ v5_orders_2(A_66)
      | ~ v4_orders_2(A_66)
      | ~ v3_orders_2(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_62,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_60])).

tff(c_65,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_32,c_62])).

tff(c_66,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_65])).

tff(c_4,plain,(
    ! [A_1,B_2,C_6] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_6),B_2)
      | r1_tarski(B_2,C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_1,B_2,C_6] :
      ( m1_subset_1('#skF_1'(A_1,B_2,C_6),A_1)
      | r1_tarski(B_2,C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_308,plain,(
    ! [A_105,B_106,C_107] :
      ( r2_hidden('#skF_2'(A_105,B_106,C_107),B_106)
      | ~ m1_orders_2(C_107,A_105,B_106)
      | k1_xboole_0 = B_106
      | ~ m1_subset_1(C_107,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_orders_2(A_105)
      | ~ v5_orders_2(A_105)
      | ~ v4_orders_2(A_105)
      | ~ v3_orders_2(A_105)
      | v2_struct_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_312,plain,(
    ! [B_106] :
      ( r2_hidden('#skF_2'('#skF_3',B_106,'#skF_5'),B_106)
      | ~ m1_orders_2('#skF_5','#skF_3',B_106)
      | k1_xboole_0 = B_106
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_66,c_308])).

tff(c_324,plain,(
    ! [B_106] :
      ( r2_hidden('#skF_2'('#skF_3',B_106,'#skF_5'),B_106)
      | ~ m1_orders_2('#skF_5','#skF_3',B_106)
      | k1_xboole_0 = B_106
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_312])).

tff(c_375,plain,(
    ! [B_114] :
      ( r2_hidden('#skF_2'('#skF_3',B_114,'#skF_5'),B_114)
      | ~ m1_orders_2('#skF_5','#skF_3',B_114)
      | k1_xboole_0 = B_114
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_324])).

tff(c_384,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | ~ m1_orders_2('#skF_5','#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32,c_375])).

tff(c_390,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_384])).

tff(c_391,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_390])).

tff(c_90,plain,(
    ! [A_73,B_74,C_75] :
      ( r2_hidden('#skF_2'(A_73,B_74,C_75),B_74)
      | ~ m1_orders_2(C_75,A_73,B_74)
      | k1_xboole_0 = B_74
      | ~ m1_subset_1(C_75,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_orders_2(A_73)
      | ~ v5_orders_2(A_73)
      | ~ v4_orders_2(A_73)
      | ~ v3_orders_2(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_92,plain,(
    ! [B_74] :
      ( r2_hidden('#skF_2'('#skF_3',B_74,'#skF_5'),B_74)
      | ~ m1_orders_2('#skF_5','#skF_3',B_74)
      | k1_xboole_0 = B_74
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_66,c_90])).

tff(c_100,plain,(
    ! [B_74] :
      ( r2_hidden('#skF_2'('#skF_3',B_74,'#skF_5'),B_74)
      | ~ m1_orders_2('#skF_5','#skF_3',B_74)
      | k1_xboole_0 = B_74
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_92])).

tff(c_125,plain,(
    ! [B_81] :
      ( r2_hidden('#skF_2'('#skF_3',B_81,'#skF_5'),B_81)
      | ~ m1_orders_2('#skF_5','#skF_3',B_81)
      | k1_xboole_0 = B_81
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_100])).

tff(c_132,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | ~ m1_orders_2('#skF_5','#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32,c_125])).

tff(c_137,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_132])).

tff(c_138,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_67,plain,(
    ! [C_68,A_69] :
      ( k1_xboole_0 = C_68
      | ~ m1_orders_2(C_68,A_69,k1_xboole_0)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_orders_2(A_69)
      | ~ v5_orders_2(A_69)
      | ~ v4_orders_2(A_69)
      | ~ v3_orders_2(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_72,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_orders_2('#skF_4','#skF_3',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_67])).

tff(c_76,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_orders_2('#skF_4','#skF_3',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_72])).

tff(c_77,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_orders_2('#skF_4','#skF_3',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_76])).

tff(c_87,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_77])).

tff(c_142,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_87])).

tff(c_147,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_142])).

tff(c_149,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_18,plain,(
    ! [A_8,B_20,C_26] :
      ( m1_subset_1('#skF_2'(A_8,B_20,C_26),u1_struct_0(A_8))
      | ~ m1_orders_2(C_26,A_8,B_20)
      | k1_xboole_0 = B_20
      | ~ m1_subset_1(C_26,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_orders_2(A_8)
      | ~ v5_orders_2(A_8)
      | ~ v4_orders_2(A_8)
      | ~ v3_orders_2(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_158,plain,(
    ! [A_91,B_92,C_93] :
      ( k3_orders_2(A_91,B_92,'#skF_2'(A_91,B_92,C_93)) = C_93
      | ~ m1_orders_2(C_93,A_91,B_92)
      | k1_xboole_0 = B_92
      | ~ m1_subset_1(C_93,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ l1_orders_2(A_91)
      | ~ v5_orders_2(A_91)
      | ~ v4_orders_2(A_91)
      | ~ v3_orders_2(A_91)
      | v2_struct_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_160,plain,(
    ! [B_92] :
      ( k3_orders_2('#skF_3',B_92,'#skF_2'('#skF_3',B_92,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_92)
      | k1_xboole_0 = B_92
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_66,c_158])).

tff(c_168,plain,(
    ! [B_92] :
      ( k3_orders_2('#skF_3',B_92,'#skF_2'('#skF_3',B_92,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_92)
      | k1_xboole_0 = B_92
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_160])).

tff(c_187,plain,(
    ! [B_95] :
      ( k3_orders_2('#skF_3',B_95,'#skF_2'('#skF_3',B_95,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_95)
      | k1_xboole_0 = B_95
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_168])).

tff(c_194,plain,
    ( k3_orders_2('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')) = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32,c_187])).

tff(c_199,plain,
    ( k3_orders_2('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_194])).

tff(c_200,plain,(
    k3_orders_2('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_199])).

tff(c_24,plain,(
    ! [B_42,D_48,A_34,C_46] :
      ( r2_hidden(B_42,D_48)
      | ~ r2_hidden(B_42,k3_orders_2(A_34,D_48,C_46))
      | ~ m1_subset_1(D_48,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ m1_subset_1(C_46,u1_struct_0(A_34))
      | ~ m1_subset_1(B_42,u1_struct_0(A_34))
      | ~ l1_orders_2(A_34)
      | ~ v5_orders_2(A_34)
      | ~ v4_orders_2(A_34)
      | ~ v3_orders_2(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_205,plain,(
    ! [B_42] :
      ( r2_hidden(B_42,'#skF_4')
      | ~ r2_hidden(B_42,'#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_42,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_24])).

tff(c_212,plain,(
    ! [B_42] :
      ( r2_hidden(B_42,'#skF_4')
      | ~ r2_hidden(B_42,'#skF_5')
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_42,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_32,c_205])).

tff(c_213,plain,(
    ! [B_42] :
      ( r2_hidden(B_42,'#skF_4')
      | ~ r2_hidden(B_42,'#skF_5')
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_42,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_212])).

tff(c_215,plain,(
    ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_213])).

tff(c_235,plain,
    ( ~ m1_orders_2('#skF_5','#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_215])).

tff(c_238,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_32,c_66,c_30,c_235])).

tff(c_240,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_149,c_238])).

tff(c_243,plain,(
    ! [B_100] :
      ( r2_hidden(B_100,'#skF_4')
      | ~ r2_hidden(B_100,'#skF_5')
      | ~ m1_subset_1(B_100,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_213])).

tff(c_265,plain,(
    ! [B_102,C_103] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_3'),B_102,C_103),'#skF_4')
      | ~ r2_hidden('#skF_1'(u1_struct_0('#skF_3'),B_102,C_103),'#skF_5')
      | r1_tarski(B_102,C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_6,c_243])).

tff(c_269,plain,(
    ! [C_6] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_3'),'#skF_5',C_6),'#skF_4')
      | r1_tarski('#skF_5',C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_4,c_265])).

tff(c_273,plain,(
    ! [C_104] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_3'),'#skF_5',C_104),'#skF_4')
      | r1_tarski('#skF_5',C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_269])).

tff(c_277,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | r1_tarski('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_273,c_2])).

tff(c_280,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_66,c_277])).

tff(c_282,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_280])).

tff(c_284,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_10,plain,(
    ! [C_26,A_8] :
      ( k1_xboole_0 = C_26
      | ~ m1_orders_2(C_26,A_8,k1_xboole_0)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_orders_2(A_8)
      | ~ v5_orders_2(A_8)
      | ~ v4_orders_2(A_8)
      | ~ v3_orders_2(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_79,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_3',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_10])).

tff(c_84,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_3',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_79])).

tff(c_85,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_3',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_84])).

tff(c_333,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_85])).

tff(c_334,plain,(
    ~ m1_orders_2('#skF_5','#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_333])).

tff(c_396,plain,(
    ~ m1_orders_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_391,c_334])).

tff(c_407,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_396])).

tff(c_409,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_390])).

tff(c_419,plain,(
    ! [A_127,B_128,C_129] :
      ( k3_orders_2(A_127,B_128,'#skF_2'(A_127,B_128,C_129)) = C_129
      | ~ m1_orders_2(C_129,A_127,B_128)
      | k1_xboole_0 = B_128
      | ~ m1_subset_1(C_129,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_orders_2(A_127)
      | ~ v5_orders_2(A_127)
      | ~ v4_orders_2(A_127)
      | ~ v3_orders_2(A_127)
      | v2_struct_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_423,plain,(
    ! [B_128] :
      ( k3_orders_2('#skF_3',B_128,'#skF_2'('#skF_3',B_128,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_128)
      | k1_xboole_0 = B_128
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_66,c_419])).

tff(c_435,plain,(
    ! [B_128] :
      ( k3_orders_2('#skF_3',B_128,'#skF_2'('#skF_3',B_128,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_128)
      | k1_xboole_0 = B_128
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_423])).

tff(c_457,plain,(
    ! [B_131] :
      ( k3_orders_2('#skF_3',B_131,'#skF_2'('#skF_3',B_131,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_131)
      | k1_xboole_0 = B_131
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_435])).

tff(c_466,plain,
    ( k3_orders_2('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')) = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32,c_457])).

tff(c_472,plain,
    ( k3_orders_2('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_466])).

tff(c_473,plain,(
    k3_orders_2('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_409,c_472])).

tff(c_501,plain,(
    ! [B_42] :
      ( r2_hidden(B_42,'#skF_4')
      | ~ r2_hidden(B_42,'#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_42,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_473,c_24])).

tff(c_508,plain,(
    ! [B_42] :
      ( r2_hidden(B_42,'#skF_4')
      | ~ r2_hidden(B_42,'#skF_5')
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_42,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_32,c_501])).

tff(c_509,plain,(
    ! [B_42] :
      ( r2_hidden(B_42,'#skF_4')
      | ~ r2_hidden(B_42,'#skF_5')
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_42,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_508])).

tff(c_511,plain,(
    ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_509])).

tff(c_514,plain,
    ( ~ m1_orders_2('#skF_5','#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_511])).

tff(c_517,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_32,c_66,c_30,c_514])).

tff(c_519,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_409,c_517])).

tff(c_540,plain,(
    ! [B_137] :
      ( r2_hidden(B_137,'#skF_4')
      | ~ r2_hidden(B_137,'#skF_5')
      | ~ m1_subset_1(B_137,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_509])).

tff(c_632,plain,(
    ! [B_149,C_150] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_3'),B_149,C_150),'#skF_4')
      | ~ r2_hidden('#skF_1'(u1_struct_0('#skF_3'),B_149,C_150),'#skF_5')
      | r1_tarski(B_149,C_150)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_149,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_6,c_540])).

tff(c_636,plain,(
    ! [C_6] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_3'),'#skF_5',C_6),'#skF_4')
      | r1_tarski('#skF_5',C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_4,c_632])).

tff(c_641,plain,(
    ! [C_153] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_3'),'#skF_5',C_153),'#skF_4')
      | r1_tarski('#skF_5',C_153)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_636])).

tff(c_645,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | r1_tarski('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_641,c_2])).

tff(c_648,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_66,c_645])).

tff(c_650,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_648])).

tff(c_651,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_333])).

tff(c_317,plain,(
    ! [B_106] :
      ( r2_hidden('#skF_2'('#skF_3',B_106,'#skF_4'),B_106)
      | ~ m1_orders_2('#skF_4','#skF_3',B_106)
      | k1_xboole_0 = B_106
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_308])).

tff(c_329,plain,(
    ! [B_106] :
      ( r2_hidden('#skF_2'('#skF_3',B_106,'#skF_4'),B_106)
      | ~ m1_orders_2('#skF_4','#skF_3',B_106)
      | k1_xboole_0 = B_106
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_317])).

tff(c_330,plain,(
    ! [B_106] :
      ( r2_hidden('#skF_2'('#skF_3',B_106,'#skF_4'),B_106)
      | ~ m1_orders_2('#skF_4','#skF_3',B_106)
      | k1_xboole_0 = B_106
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_329])).

tff(c_680,plain,(
    ! [B_158] :
      ( r2_hidden('#skF_2'('#skF_3',B_158,'#skF_4'),B_158)
      | ~ m1_orders_2('#skF_4','#skF_3',B_158)
      | B_158 = '#skF_5'
      | ~ m1_subset_1(B_158,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_651,c_330])).

tff(c_690,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_4'),'#skF_4')
    | ~ m1_orders_2('#skF_4','#skF_3','#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32,c_680])).

tff(c_691,plain,(
    ~ m1_orders_2('#skF_4','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_690])).

tff(c_325,plain,(
    ! [B_106] :
      ( r2_hidden('#skF_2'('#skF_3',B_106,'#skF_5'),B_106)
      | ~ m1_orders_2('#skF_5','#skF_3',B_106)
      | k1_xboole_0 = B_106
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_324])).

tff(c_693,plain,(
    ! [B_159] :
      ( r2_hidden('#skF_2'('#skF_3',B_159,'#skF_5'),B_159)
      | ~ m1_orders_2('#skF_5','#skF_3',B_159)
      | B_159 = '#skF_5'
      | ~ m1_subset_1(B_159,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_651,c_325])).

tff(c_700,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | ~ m1_orders_2('#skF_5','#skF_3','#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32,c_693])).

tff(c_708,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_700])).

tff(c_709,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_708])).

tff(c_652,plain,(
    m1_orders_2('#skF_5','#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_333])).

tff(c_666,plain,(
    m1_orders_2('#skF_5','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_651,c_652])).

tff(c_713,plain,(
    m1_orders_2('#skF_4','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_709,c_709,c_666])).

tff(c_720,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_691,c_713])).

tff(c_722,plain,(
    '#skF_5' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_708])).

tff(c_774,plain,(
    ! [A_8,B_20,C_26] :
      ( m1_subset_1('#skF_2'(A_8,B_20,C_26),u1_struct_0(A_8))
      | ~ m1_orders_2(C_26,A_8,B_20)
      | B_20 = '#skF_5'
      | ~ m1_subset_1(C_26,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_orders_2(A_8)
      | ~ v5_orders_2(A_8)
      | ~ v4_orders_2(A_8)
      | ~ v3_orders_2(A_8)
      | v2_struct_0(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_651,c_18])).

tff(c_14,plain,(
    ! [A_8,B_20,C_26] :
      ( k3_orders_2(A_8,B_20,'#skF_2'(A_8,B_20,C_26)) = C_26
      | ~ m1_orders_2(C_26,A_8,B_20)
      | k1_xboole_0 = B_20
      | ~ m1_subset_1(C_26,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_orders_2(A_8)
      | ~ v5_orders_2(A_8)
      | ~ v4_orders_2(A_8)
      | ~ v3_orders_2(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_777,plain,(
    ! [A_178,B_179,C_180] :
      ( k3_orders_2(A_178,B_179,'#skF_2'(A_178,B_179,C_180)) = C_180
      | ~ m1_orders_2(C_180,A_178,B_179)
      | B_179 = '#skF_5'
      | ~ m1_subset_1(C_180,k1_zfmisc_1(u1_struct_0(A_178)))
      | ~ m1_subset_1(B_179,k1_zfmisc_1(u1_struct_0(A_178)))
      | ~ l1_orders_2(A_178)
      | ~ v5_orders_2(A_178)
      | ~ v4_orders_2(A_178)
      | ~ v3_orders_2(A_178)
      | v2_struct_0(A_178) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_651,c_14])).

tff(c_779,plain,(
    ! [B_179] :
      ( k3_orders_2('#skF_3',B_179,'#skF_2'('#skF_3',B_179,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_179)
      | B_179 = '#skF_5'
      | ~ m1_subset_1(B_179,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_66,c_777])).

tff(c_787,plain,(
    ! [B_179] :
      ( k3_orders_2('#skF_3',B_179,'#skF_2'('#skF_3',B_179,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_179)
      | B_179 = '#skF_5'
      | ~ m1_subset_1(B_179,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_779])).

tff(c_794,plain,(
    ! [B_181] :
      ( k3_orders_2('#skF_3',B_181,'#skF_2'('#skF_3',B_181,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_181)
      | B_181 = '#skF_5'
      | ~ m1_subset_1(B_181,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_787])).

tff(c_801,plain,
    ( k3_orders_2('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')) = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_3','#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32,c_794])).

tff(c_809,plain,
    ( k3_orders_2('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')) = '#skF_5'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_801])).

tff(c_810,plain,(
    k3_orders_2('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_722,c_809])).

tff(c_815,plain,(
    ! [B_42] :
      ( r2_hidden(B_42,'#skF_4')
      | ~ r2_hidden(B_42,'#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_42,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_810,c_24])).

tff(c_822,plain,(
    ! [B_42] :
      ( r2_hidden(B_42,'#skF_4')
      | ~ r2_hidden(B_42,'#skF_5')
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_42,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_32,c_815])).

tff(c_823,plain,(
    ! [B_42] :
      ( r2_hidden(B_42,'#skF_4')
      | ~ r2_hidden(B_42,'#skF_5')
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_42,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_822])).

tff(c_842,plain,(
    ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_823])).

tff(c_845,plain,
    ( ~ m1_orders_2('#skF_5','#skF_3','#skF_4')
    | '#skF_5' = '#skF_4'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_774,c_842])).

tff(c_848,plain,
    ( '#skF_5' = '#skF_4'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_32,c_66,c_30,c_845])).

tff(c_850,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_722,c_848])).

tff(c_865,plain,(
    ! [B_187] :
      ( r2_hidden(B_187,'#skF_4')
      | ~ r2_hidden(B_187,'#skF_5')
      | ~ m1_subset_1(B_187,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_823])).

tff(c_940,plain,(
    ! [B_197,C_198] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_3'),B_197,C_198),'#skF_4')
      | ~ r2_hidden('#skF_1'(u1_struct_0('#skF_3'),B_197,C_198),'#skF_5')
      | r1_tarski(B_197,C_198)
      | ~ m1_subset_1(C_198,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_197,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_6,c_865])).

tff(c_944,plain,(
    ! [C_6] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_3'),'#skF_5',C_6),'#skF_4')
      | r1_tarski('#skF_5',C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_4,c_940])).

tff(c_948,plain,(
    ! [C_199] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_3'),'#skF_5',C_199),'#skF_4')
      | r1_tarski('#skF_5',C_199)
      | ~ m1_subset_1(C_199,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_944])).

tff(c_952,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | r1_tarski('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_948,c_2])).

tff(c_955,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_66,c_952])).

tff(c_957,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_955])).

tff(c_959,plain,(
    m1_orders_2('#skF_4','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_690])).

tff(c_967,plain,(
    ! [B_200] :
      ( r2_hidden('#skF_2'('#skF_3',B_200,'#skF_5'),B_200)
      | ~ m1_orders_2('#skF_5','#skF_3',B_200)
      | B_200 = '#skF_5'
      | ~ m1_subset_1(B_200,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_651,c_325])).

tff(c_974,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | ~ m1_orders_2('#skF_5','#skF_3','#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32,c_967])).

tff(c_982,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_974])).

tff(c_984,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_982])).

tff(c_283,plain,
    ( ~ m1_orders_2('#skF_4','#skF_3',k1_xboole_0)
    | k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_331,plain,(
    ~ m1_orders_2('#skF_4','#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_283])).

tff(c_653,plain,(
    ~ m1_orders_2('#skF_4','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_651,c_331])).

tff(c_987,plain,(
    ~ m1_orders_2('#skF_4','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_984,c_653])).

tff(c_996,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_959,c_987])).

tff(c_998,plain,(
    '#skF_5' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_982])).

tff(c_1050,plain,(
    ! [A_8,B_20,C_26] :
      ( m1_subset_1('#skF_2'(A_8,B_20,C_26),u1_struct_0(A_8))
      | ~ m1_orders_2(C_26,A_8,B_20)
      | B_20 = '#skF_5'
      | ~ m1_subset_1(C_26,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_orders_2(A_8)
      | ~ v5_orders_2(A_8)
      | ~ v4_orders_2(A_8)
      | ~ v3_orders_2(A_8)
      | v2_struct_0(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_651,c_18])).

tff(c_1053,plain,(
    ! [A_219,B_220,C_221] :
      ( k3_orders_2(A_219,B_220,'#skF_2'(A_219,B_220,C_221)) = C_221
      | ~ m1_orders_2(C_221,A_219,B_220)
      | B_220 = '#skF_5'
      | ~ m1_subset_1(C_221,k1_zfmisc_1(u1_struct_0(A_219)))
      | ~ m1_subset_1(B_220,k1_zfmisc_1(u1_struct_0(A_219)))
      | ~ l1_orders_2(A_219)
      | ~ v5_orders_2(A_219)
      | ~ v4_orders_2(A_219)
      | ~ v3_orders_2(A_219)
      | v2_struct_0(A_219) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_651,c_14])).

tff(c_1055,plain,(
    ! [B_220] :
      ( k3_orders_2('#skF_3',B_220,'#skF_2'('#skF_3',B_220,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_220)
      | B_220 = '#skF_5'
      | ~ m1_subset_1(B_220,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_66,c_1053])).

tff(c_1063,plain,(
    ! [B_220] :
      ( k3_orders_2('#skF_3',B_220,'#skF_2'('#skF_3',B_220,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_220)
      | B_220 = '#skF_5'
      | ~ m1_subset_1(B_220,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_1055])).

tff(c_1087,plain,(
    ! [B_226] :
      ( k3_orders_2('#skF_3',B_226,'#skF_2'('#skF_3',B_226,'#skF_5')) = '#skF_5'
      | ~ m1_orders_2('#skF_5','#skF_3',B_226)
      | B_226 = '#skF_5'
      | ~ m1_subset_1(B_226,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1063])).

tff(c_1094,plain,
    ( k3_orders_2('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')) = '#skF_5'
    | ~ m1_orders_2('#skF_5','#skF_3','#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32,c_1087])).

tff(c_1102,plain,
    ( k3_orders_2('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')) = '#skF_5'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1094])).

tff(c_1103,plain,(
    k3_orders_2('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_998,c_1102])).

tff(c_1108,plain,(
    ! [B_42] :
      ( r2_hidden(B_42,'#skF_4')
      | ~ r2_hidden(B_42,'#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_42,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1103,c_24])).

tff(c_1115,plain,(
    ! [B_42] :
      ( r2_hidden(B_42,'#skF_4')
      | ~ r2_hidden(B_42,'#skF_5')
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_42,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_32,c_1108])).

tff(c_1116,plain,(
    ! [B_42] :
      ( r2_hidden(B_42,'#skF_4')
      | ~ r2_hidden(B_42,'#skF_5')
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_42,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1115])).

tff(c_1118,plain,(
    ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1116])).

tff(c_1135,plain,
    ( ~ m1_orders_2('#skF_5','#skF_3','#skF_4')
    | '#skF_5' = '#skF_4'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1050,c_1118])).

tff(c_1138,plain,
    ( '#skF_5' = '#skF_4'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_32,c_66,c_30,c_1135])).

tff(c_1140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_998,c_1138])).

tff(c_1143,plain,(
    ! [B_228] :
      ( r2_hidden(B_228,'#skF_4')
      | ~ r2_hidden(B_228,'#skF_5')
      | ~ m1_subset_1(B_228,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_1116])).

tff(c_1271,plain,(
    ! [B_240,C_241] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_3'),B_240,C_241),'#skF_4')
      | ~ r2_hidden('#skF_1'(u1_struct_0('#skF_3'),B_240,C_241),'#skF_5')
      | r1_tarski(B_240,C_241)
      | ~ m1_subset_1(C_241,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_240,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_6,c_1143])).

tff(c_1275,plain,(
    ! [C_6] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_3'),'#skF_5',C_6),'#skF_4')
      | r1_tarski('#skF_5',C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_4,c_1271])).

tff(c_1281,plain,(
    ! [C_245] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_3'),'#skF_5',C_245),'#skF_4')
      | r1_tarski('#skF_5',C_245)
      | ~ m1_subset_1(C_245,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1275])).

tff(c_1285,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | r1_tarski('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_1281,c_2])).

tff(c_1288,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_66,c_1285])).

tff(c_1290,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_1288])).

tff(c_1291,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_283])).

tff(c_1313,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1291,c_30,c_1291,c_1291,c_85])).

tff(c_1317,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1313,c_28])).

tff(c_1323,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1317])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:38:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.95/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/1.66  
% 3.95/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/1.66  %$ r2_orders_2 > m1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 3.95/1.66  
% 3.95/1.66  %Foreground sorts:
% 3.95/1.66  
% 3.95/1.66  
% 3.95/1.66  %Background operators:
% 3.95/1.66  
% 3.95/1.66  
% 3.95/1.66  %Foreground operators:
% 3.95/1.66  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.95/1.66  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.95/1.66  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.95/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.95/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.95/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.95/1.66  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 3.95/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.95/1.66  tff('#skF_5', type, '#skF_5': $i).
% 3.95/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.95/1.66  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.95/1.66  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.95/1.66  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.95/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.95/1.66  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.95/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.95/1.66  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 3.95/1.66  tff('#skF_4', type, '#skF_4': $i).
% 3.95/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.95/1.66  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 3.95/1.66  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.95/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.95/1.66  
% 3.95/1.70  tff(f_138, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_orders_2)).
% 3.95/1.70  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_subset_1)).
% 3.95/1.70  tff(f_92, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_orders_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_orders_2)).
% 3.95/1.70  tff(f_74, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((~(B = k1_xboole_0) => (m1_orders_2(C, A, B) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(A)) & r2_hidden(D, B)) & (C = k3_orders_2(A, B, D)))))) & ((B = k1_xboole_0) => (m1_orders_2(C, A, B) <=> (C = k1_xboole_0)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d15_orders_2)).
% 3.95/1.70  tff(f_118, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 3.95/1.70  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.95/1.70  tff(c_45, plain, (![A_59, B_60, C_61]: (r2_hidden('#skF_1'(A_59, B_60, C_61), B_60) | r1_tarski(B_60, C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(A_59)) | ~m1_subset_1(B_60, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.95/1.70  tff(c_2, plain, (![A_1, B_2, C_6]: (~r2_hidden('#skF_1'(A_1, B_2, C_6), C_6) | r1_tarski(B_2, C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.95/1.70  tff(c_51, plain, (![B_62, A_63]: (r1_tarski(B_62, B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(A_63)))), inference(resolution, [status(thm)], [c_45, c_2])).
% 3.95/1.70  tff(c_58, plain, (r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_51])).
% 3.95/1.70  tff(c_28, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.95/1.70  tff(c_42, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.95/1.70  tff(c_40, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.95/1.70  tff(c_38, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.95/1.70  tff(c_36, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.95/1.70  tff(c_34, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.95/1.70  tff(c_30, plain, (m1_orders_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.95/1.70  tff(c_60, plain, (![C_65, A_66, B_67]: (m1_subset_1(C_65, k1_zfmisc_1(u1_struct_0(A_66))) | ~m1_orders_2(C_65, A_66, B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_orders_2(A_66) | ~v5_orders_2(A_66) | ~v4_orders_2(A_66) | ~v3_orders_2(A_66) | v2_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.95/1.70  tff(c_62, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_30, c_60])).
% 3.95/1.70  tff(c_65, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_32, c_62])).
% 3.95/1.70  tff(c_66, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_42, c_65])).
% 3.95/1.70  tff(c_4, plain, (![A_1, B_2, C_6]: (r2_hidden('#skF_1'(A_1, B_2, C_6), B_2) | r1_tarski(B_2, C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.95/1.70  tff(c_6, plain, (![A_1, B_2, C_6]: (m1_subset_1('#skF_1'(A_1, B_2, C_6), A_1) | r1_tarski(B_2, C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.95/1.70  tff(c_308, plain, (![A_105, B_106, C_107]: (r2_hidden('#skF_2'(A_105, B_106, C_107), B_106) | ~m1_orders_2(C_107, A_105, B_106) | k1_xboole_0=B_106 | ~m1_subset_1(C_107, k1_zfmisc_1(u1_struct_0(A_105))) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_orders_2(A_105) | ~v5_orders_2(A_105) | ~v4_orders_2(A_105) | ~v3_orders_2(A_105) | v2_struct_0(A_105))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.95/1.70  tff(c_312, plain, (![B_106]: (r2_hidden('#skF_2'('#skF_3', B_106, '#skF_5'), B_106) | ~m1_orders_2('#skF_5', '#skF_3', B_106) | k1_xboole_0=B_106 | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_66, c_308])).
% 3.95/1.70  tff(c_324, plain, (![B_106]: (r2_hidden('#skF_2'('#skF_3', B_106, '#skF_5'), B_106) | ~m1_orders_2('#skF_5', '#skF_3', B_106) | k1_xboole_0=B_106 | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_312])).
% 3.95/1.70  tff(c_375, plain, (![B_114]: (r2_hidden('#skF_2'('#skF_3', B_114, '#skF_5'), B_114) | ~m1_orders_2('#skF_5', '#skF_3', B_114) | k1_xboole_0=B_114 | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_324])).
% 3.95/1.70  tff(c_384, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | ~m1_orders_2('#skF_5', '#skF_3', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_32, c_375])).
% 3.95/1.70  tff(c_390, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_384])).
% 3.95/1.70  tff(c_391, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_390])).
% 3.95/1.70  tff(c_90, plain, (![A_73, B_74, C_75]: (r2_hidden('#skF_2'(A_73, B_74, C_75), B_74) | ~m1_orders_2(C_75, A_73, B_74) | k1_xboole_0=B_74 | ~m1_subset_1(C_75, k1_zfmisc_1(u1_struct_0(A_73))) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_orders_2(A_73) | ~v5_orders_2(A_73) | ~v4_orders_2(A_73) | ~v3_orders_2(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.95/1.70  tff(c_92, plain, (![B_74]: (r2_hidden('#skF_2'('#skF_3', B_74, '#skF_5'), B_74) | ~m1_orders_2('#skF_5', '#skF_3', B_74) | k1_xboole_0=B_74 | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_66, c_90])).
% 3.95/1.70  tff(c_100, plain, (![B_74]: (r2_hidden('#skF_2'('#skF_3', B_74, '#skF_5'), B_74) | ~m1_orders_2('#skF_5', '#skF_3', B_74) | k1_xboole_0=B_74 | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_92])).
% 3.95/1.70  tff(c_125, plain, (![B_81]: (r2_hidden('#skF_2'('#skF_3', B_81, '#skF_5'), B_81) | ~m1_orders_2('#skF_5', '#skF_3', B_81) | k1_xboole_0=B_81 | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_100])).
% 3.95/1.70  tff(c_132, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | ~m1_orders_2('#skF_5', '#skF_3', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_32, c_125])).
% 3.95/1.70  tff(c_137, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_132])).
% 3.95/1.70  tff(c_138, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_137])).
% 3.95/1.70  tff(c_67, plain, (![C_68, A_69]: (k1_xboole_0=C_68 | ~m1_orders_2(C_68, A_69, k1_xboole_0) | ~m1_subset_1(C_68, k1_zfmisc_1(u1_struct_0(A_69))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_orders_2(A_69) | ~v5_orders_2(A_69) | ~v4_orders_2(A_69) | ~v3_orders_2(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.95/1.70  tff(c_72, plain, (k1_xboole_0='#skF_4' | ~m1_orders_2('#skF_4', '#skF_3', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_32, c_67])).
% 3.95/1.70  tff(c_76, plain, (k1_xboole_0='#skF_4' | ~m1_orders_2('#skF_4', '#skF_3', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_72])).
% 3.95/1.70  tff(c_77, plain, (k1_xboole_0='#skF_4' | ~m1_orders_2('#skF_4', '#skF_3', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_42, c_76])).
% 3.95/1.70  tff(c_87, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_77])).
% 3.95/1.70  tff(c_142, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_87])).
% 3.95/1.70  tff(c_147, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_142])).
% 3.95/1.70  tff(c_149, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_137])).
% 3.95/1.70  tff(c_18, plain, (![A_8, B_20, C_26]: (m1_subset_1('#skF_2'(A_8, B_20, C_26), u1_struct_0(A_8)) | ~m1_orders_2(C_26, A_8, B_20) | k1_xboole_0=B_20 | ~m1_subset_1(C_26, k1_zfmisc_1(u1_struct_0(A_8))) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_orders_2(A_8) | ~v5_orders_2(A_8) | ~v4_orders_2(A_8) | ~v3_orders_2(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.95/1.70  tff(c_158, plain, (![A_91, B_92, C_93]: (k3_orders_2(A_91, B_92, '#skF_2'(A_91, B_92, C_93))=C_93 | ~m1_orders_2(C_93, A_91, B_92) | k1_xboole_0=B_92 | ~m1_subset_1(C_93, k1_zfmisc_1(u1_struct_0(A_91))) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_91))) | ~l1_orders_2(A_91) | ~v5_orders_2(A_91) | ~v4_orders_2(A_91) | ~v3_orders_2(A_91) | v2_struct_0(A_91))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.95/1.70  tff(c_160, plain, (![B_92]: (k3_orders_2('#skF_3', B_92, '#skF_2'('#skF_3', B_92, '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', B_92) | k1_xboole_0=B_92 | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_66, c_158])).
% 3.95/1.70  tff(c_168, plain, (![B_92]: (k3_orders_2('#skF_3', B_92, '#skF_2'('#skF_3', B_92, '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', B_92) | k1_xboole_0=B_92 | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_160])).
% 3.95/1.70  tff(c_187, plain, (![B_95]: (k3_orders_2('#skF_3', B_95, '#skF_2'('#skF_3', B_95, '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', B_95) | k1_xboole_0=B_95 | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_168])).
% 3.95/1.70  tff(c_194, plain, (k3_orders_2('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_32, c_187])).
% 3.95/1.70  tff(c_199, plain, (k3_orders_2('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_194])).
% 3.95/1.70  tff(c_200, plain, (k3_orders_2('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_149, c_199])).
% 3.95/1.70  tff(c_24, plain, (![B_42, D_48, A_34, C_46]: (r2_hidden(B_42, D_48) | ~r2_hidden(B_42, k3_orders_2(A_34, D_48, C_46)) | ~m1_subset_1(D_48, k1_zfmisc_1(u1_struct_0(A_34))) | ~m1_subset_1(C_46, u1_struct_0(A_34)) | ~m1_subset_1(B_42, u1_struct_0(A_34)) | ~l1_orders_2(A_34) | ~v5_orders_2(A_34) | ~v4_orders_2(A_34) | ~v3_orders_2(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.95/1.70  tff(c_205, plain, (![B_42]: (r2_hidden(B_42, '#skF_4') | ~r2_hidden(B_42, '#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1(B_42, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_200, c_24])).
% 3.95/1.70  tff(c_212, plain, (![B_42]: (r2_hidden(B_42, '#skF_4') | ~r2_hidden(B_42, '#skF_5') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1(B_42, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_32, c_205])).
% 3.95/1.70  tff(c_213, plain, (![B_42]: (r2_hidden(B_42, '#skF_4') | ~r2_hidden(B_42, '#skF_5') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1(B_42, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_42, c_212])).
% 3.95/1.70  tff(c_215, plain, (~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_213])).
% 3.95/1.70  tff(c_235, plain, (~m1_orders_2('#skF_5', '#skF_3', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_18, c_215])).
% 3.95/1.70  tff(c_238, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_32, c_66, c_30, c_235])).
% 3.95/1.70  tff(c_240, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_149, c_238])).
% 3.95/1.70  tff(c_243, plain, (![B_100]: (r2_hidden(B_100, '#skF_4') | ~r2_hidden(B_100, '#skF_5') | ~m1_subset_1(B_100, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_213])).
% 3.95/1.70  tff(c_265, plain, (![B_102, C_103]: (r2_hidden('#skF_1'(u1_struct_0('#skF_3'), B_102, C_103), '#skF_4') | ~r2_hidden('#skF_1'(u1_struct_0('#skF_3'), B_102, C_103), '#skF_5') | r1_tarski(B_102, C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_6, c_243])).
% 3.95/1.70  tff(c_269, plain, (![C_6]: (r2_hidden('#skF_1'(u1_struct_0('#skF_3'), '#skF_5', C_6), '#skF_4') | r1_tarski('#skF_5', C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_4, c_265])).
% 3.95/1.70  tff(c_273, plain, (![C_104]: (r2_hidden('#skF_1'(u1_struct_0('#skF_3'), '#skF_5', C_104), '#skF_4') | r1_tarski('#skF_5', C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_269])).
% 3.95/1.70  tff(c_277, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | r1_tarski('#skF_5', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_273, c_2])).
% 3.95/1.70  tff(c_280, plain, (r1_tarski('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_66, c_277])).
% 3.95/1.70  tff(c_282, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_280])).
% 3.95/1.70  tff(c_284, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_77])).
% 3.95/1.70  tff(c_10, plain, (![C_26, A_8]: (k1_xboole_0=C_26 | ~m1_orders_2(C_26, A_8, k1_xboole_0) | ~m1_subset_1(C_26, k1_zfmisc_1(u1_struct_0(A_8))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_orders_2(A_8) | ~v5_orders_2(A_8) | ~v4_orders_2(A_8) | ~v3_orders_2(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.95/1.70  tff(c_79, plain, (k1_xboole_0='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_66, c_10])).
% 3.95/1.70  tff(c_84, plain, (k1_xboole_0='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_79])).
% 3.95/1.70  tff(c_85, plain, (k1_xboole_0='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_42, c_84])).
% 3.95/1.70  tff(c_333, plain, (k1_xboole_0='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_284, c_85])).
% 3.95/1.70  tff(c_334, plain, (~m1_orders_2('#skF_5', '#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_333])).
% 3.95/1.70  tff(c_396, plain, (~m1_orders_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_391, c_334])).
% 3.95/1.70  tff(c_407, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_396])).
% 3.95/1.70  tff(c_409, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_390])).
% 3.95/1.70  tff(c_419, plain, (![A_127, B_128, C_129]: (k3_orders_2(A_127, B_128, '#skF_2'(A_127, B_128, C_129))=C_129 | ~m1_orders_2(C_129, A_127, B_128) | k1_xboole_0=B_128 | ~m1_subset_1(C_129, k1_zfmisc_1(u1_struct_0(A_127))) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0(A_127))) | ~l1_orders_2(A_127) | ~v5_orders_2(A_127) | ~v4_orders_2(A_127) | ~v3_orders_2(A_127) | v2_struct_0(A_127))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.95/1.70  tff(c_423, plain, (![B_128]: (k3_orders_2('#skF_3', B_128, '#skF_2'('#skF_3', B_128, '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', B_128) | k1_xboole_0=B_128 | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_66, c_419])).
% 3.95/1.70  tff(c_435, plain, (![B_128]: (k3_orders_2('#skF_3', B_128, '#skF_2'('#skF_3', B_128, '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', B_128) | k1_xboole_0=B_128 | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_423])).
% 3.95/1.70  tff(c_457, plain, (![B_131]: (k3_orders_2('#skF_3', B_131, '#skF_2'('#skF_3', B_131, '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', B_131) | k1_xboole_0=B_131 | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_435])).
% 3.95/1.70  tff(c_466, plain, (k3_orders_2('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_32, c_457])).
% 3.95/1.70  tff(c_472, plain, (k3_orders_2('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_466])).
% 3.95/1.70  tff(c_473, plain, (k3_orders_2('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_409, c_472])).
% 3.95/1.70  tff(c_501, plain, (![B_42]: (r2_hidden(B_42, '#skF_4') | ~r2_hidden(B_42, '#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1(B_42, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_473, c_24])).
% 3.95/1.70  tff(c_508, plain, (![B_42]: (r2_hidden(B_42, '#skF_4') | ~r2_hidden(B_42, '#skF_5') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1(B_42, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_32, c_501])).
% 3.95/1.70  tff(c_509, plain, (![B_42]: (r2_hidden(B_42, '#skF_4') | ~r2_hidden(B_42, '#skF_5') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1(B_42, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_42, c_508])).
% 3.95/1.70  tff(c_511, plain, (~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_509])).
% 3.95/1.70  tff(c_514, plain, (~m1_orders_2('#skF_5', '#skF_3', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_18, c_511])).
% 3.95/1.70  tff(c_517, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_32, c_66, c_30, c_514])).
% 3.95/1.70  tff(c_519, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_409, c_517])).
% 3.95/1.70  tff(c_540, plain, (![B_137]: (r2_hidden(B_137, '#skF_4') | ~r2_hidden(B_137, '#skF_5') | ~m1_subset_1(B_137, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_509])).
% 3.95/1.70  tff(c_632, plain, (![B_149, C_150]: (r2_hidden('#skF_1'(u1_struct_0('#skF_3'), B_149, C_150), '#skF_4') | ~r2_hidden('#skF_1'(u1_struct_0('#skF_3'), B_149, C_150), '#skF_5') | r1_tarski(B_149, C_150) | ~m1_subset_1(C_150, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_149, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_6, c_540])).
% 3.95/1.70  tff(c_636, plain, (![C_6]: (r2_hidden('#skF_1'(u1_struct_0('#skF_3'), '#skF_5', C_6), '#skF_4') | r1_tarski('#skF_5', C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_4, c_632])).
% 3.95/1.70  tff(c_641, plain, (![C_153]: (r2_hidden('#skF_1'(u1_struct_0('#skF_3'), '#skF_5', C_153), '#skF_4') | r1_tarski('#skF_5', C_153) | ~m1_subset_1(C_153, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_636])).
% 3.95/1.70  tff(c_645, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | r1_tarski('#skF_5', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_641, c_2])).
% 3.95/1.70  tff(c_648, plain, (r1_tarski('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_66, c_645])).
% 3.95/1.70  tff(c_650, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_648])).
% 3.95/1.70  tff(c_651, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_333])).
% 3.95/1.70  tff(c_317, plain, (![B_106]: (r2_hidden('#skF_2'('#skF_3', B_106, '#skF_4'), B_106) | ~m1_orders_2('#skF_4', '#skF_3', B_106) | k1_xboole_0=B_106 | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_32, c_308])).
% 3.95/1.70  tff(c_329, plain, (![B_106]: (r2_hidden('#skF_2'('#skF_3', B_106, '#skF_4'), B_106) | ~m1_orders_2('#skF_4', '#skF_3', B_106) | k1_xboole_0=B_106 | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_317])).
% 3.95/1.70  tff(c_330, plain, (![B_106]: (r2_hidden('#skF_2'('#skF_3', B_106, '#skF_4'), B_106) | ~m1_orders_2('#skF_4', '#skF_3', B_106) | k1_xboole_0=B_106 | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_329])).
% 3.95/1.70  tff(c_680, plain, (![B_158]: (r2_hidden('#skF_2'('#skF_3', B_158, '#skF_4'), B_158) | ~m1_orders_2('#skF_4', '#skF_3', B_158) | B_158='#skF_5' | ~m1_subset_1(B_158, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_651, c_330])).
% 3.95/1.70  tff(c_690, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_4'), '#skF_4') | ~m1_orders_2('#skF_4', '#skF_3', '#skF_4') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_32, c_680])).
% 3.95/1.70  tff(c_691, plain, (~m1_orders_2('#skF_4', '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_690])).
% 3.95/1.70  tff(c_325, plain, (![B_106]: (r2_hidden('#skF_2'('#skF_3', B_106, '#skF_5'), B_106) | ~m1_orders_2('#skF_5', '#skF_3', B_106) | k1_xboole_0=B_106 | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_324])).
% 3.95/1.70  tff(c_693, plain, (![B_159]: (r2_hidden('#skF_2'('#skF_3', B_159, '#skF_5'), B_159) | ~m1_orders_2('#skF_5', '#skF_3', B_159) | B_159='#skF_5' | ~m1_subset_1(B_159, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_651, c_325])).
% 3.95/1.70  tff(c_700, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | ~m1_orders_2('#skF_5', '#skF_3', '#skF_4') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_32, c_693])).
% 3.95/1.70  tff(c_708, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_700])).
% 3.95/1.70  tff(c_709, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_708])).
% 3.95/1.70  tff(c_652, plain, (m1_orders_2('#skF_5', '#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_333])).
% 3.95/1.70  tff(c_666, plain, (m1_orders_2('#skF_5', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_651, c_652])).
% 3.95/1.70  tff(c_713, plain, (m1_orders_2('#skF_4', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_709, c_709, c_666])).
% 3.95/1.70  tff(c_720, plain, $false, inference(negUnitSimplification, [status(thm)], [c_691, c_713])).
% 3.95/1.70  tff(c_722, plain, ('#skF_5'!='#skF_4'), inference(splitRight, [status(thm)], [c_708])).
% 3.95/1.70  tff(c_774, plain, (![A_8, B_20, C_26]: (m1_subset_1('#skF_2'(A_8, B_20, C_26), u1_struct_0(A_8)) | ~m1_orders_2(C_26, A_8, B_20) | B_20='#skF_5' | ~m1_subset_1(C_26, k1_zfmisc_1(u1_struct_0(A_8))) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_orders_2(A_8) | ~v5_orders_2(A_8) | ~v4_orders_2(A_8) | ~v3_orders_2(A_8) | v2_struct_0(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_651, c_18])).
% 3.95/1.70  tff(c_14, plain, (![A_8, B_20, C_26]: (k3_orders_2(A_8, B_20, '#skF_2'(A_8, B_20, C_26))=C_26 | ~m1_orders_2(C_26, A_8, B_20) | k1_xboole_0=B_20 | ~m1_subset_1(C_26, k1_zfmisc_1(u1_struct_0(A_8))) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_orders_2(A_8) | ~v5_orders_2(A_8) | ~v4_orders_2(A_8) | ~v3_orders_2(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.95/1.70  tff(c_777, plain, (![A_178, B_179, C_180]: (k3_orders_2(A_178, B_179, '#skF_2'(A_178, B_179, C_180))=C_180 | ~m1_orders_2(C_180, A_178, B_179) | B_179='#skF_5' | ~m1_subset_1(C_180, k1_zfmisc_1(u1_struct_0(A_178))) | ~m1_subset_1(B_179, k1_zfmisc_1(u1_struct_0(A_178))) | ~l1_orders_2(A_178) | ~v5_orders_2(A_178) | ~v4_orders_2(A_178) | ~v3_orders_2(A_178) | v2_struct_0(A_178))), inference(demodulation, [status(thm), theory('equality')], [c_651, c_14])).
% 3.95/1.70  tff(c_779, plain, (![B_179]: (k3_orders_2('#skF_3', B_179, '#skF_2'('#skF_3', B_179, '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', B_179) | B_179='#skF_5' | ~m1_subset_1(B_179, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_66, c_777])).
% 3.95/1.70  tff(c_787, plain, (![B_179]: (k3_orders_2('#skF_3', B_179, '#skF_2'('#skF_3', B_179, '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', B_179) | B_179='#skF_5' | ~m1_subset_1(B_179, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_779])).
% 3.95/1.70  tff(c_794, plain, (![B_181]: (k3_orders_2('#skF_3', B_181, '#skF_2'('#skF_3', B_181, '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', B_181) | B_181='#skF_5' | ~m1_subset_1(B_181, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_787])).
% 3.95/1.70  tff(c_801, plain, (k3_orders_2('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', '#skF_4') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_32, c_794])).
% 3.95/1.70  tff(c_809, plain, (k3_orders_2('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))='#skF_5' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_801])).
% 3.95/1.70  tff(c_810, plain, (k3_orders_2('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_722, c_809])).
% 3.95/1.70  tff(c_815, plain, (![B_42]: (r2_hidden(B_42, '#skF_4') | ~r2_hidden(B_42, '#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1(B_42, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_810, c_24])).
% 3.95/1.70  tff(c_822, plain, (![B_42]: (r2_hidden(B_42, '#skF_4') | ~r2_hidden(B_42, '#skF_5') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1(B_42, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_32, c_815])).
% 3.95/1.70  tff(c_823, plain, (![B_42]: (r2_hidden(B_42, '#skF_4') | ~r2_hidden(B_42, '#skF_5') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1(B_42, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_42, c_822])).
% 3.95/1.70  tff(c_842, plain, (~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_823])).
% 3.95/1.70  tff(c_845, plain, (~m1_orders_2('#skF_5', '#skF_3', '#skF_4') | '#skF_5'='#skF_4' | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_774, c_842])).
% 3.95/1.70  tff(c_848, plain, ('#skF_5'='#skF_4' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_32, c_66, c_30, c_845])).
% 3.95/1.70  tff(c_850, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_722, c_848])).
% 3.95/1.70  tff(c_865, plain, (![B_187]: (r2_hidden(B_187, '#skF_4') | ~r2_hidden(B_187, '#skF_5') | ~m1_subset_1(B_187, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_823])).
% 3.95/1.70  tff(c_940, plain, (![B_197, C_198]: (r2_hidden('#skF_1'(u1_struct_0('#skF_3'), B_197, C_198), '#skF_4') | ~r2_hidden('#skF_1'(u1_struct_0('#skF_3'), B_197, C_198), '#skF_5') | r1_tarski(B_197, C_198) | ~m1_subset_1(C_198, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_197, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_6, c_865])).
% 3.95/1.70  tff(c_944, plain, (![C_6]: (r2_hidden('#skF_1'(u1_struct_0('#skF_3'), '#skF_5', C_6), '#skF_4') | r1_tarski('#skF_5', C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_4, c_940])).
% 3.95/1.70  tff(c_948, plain, (![C_199]: (r2_hidden('#skF_1'(u1_struct_0('#skF_3'), '#skF_5', C_199), '#skF_4') | r1_tarski('#skF_5', C_199) | ~m1_subset_1(C_199, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_944])).
% 3.95/1.70  tff(c_952, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | r1_tarski('#skF_5', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_948, c_2])).
% 3.95/1.70  tff(c_955, plain, (r1_tarski('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_66, c_952])).
% 3.95/1.70  tff(c_957, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_955])).
% 3.95/1.70  tff(c_959, plain, (m1_orders_2('#skF_4', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_690])).
% 3.95/1.70  tff(c_967, plain, (![B_200]: (r2_hidden('#skF_2'('#skF_3', B_200, '#skF_5'), B_200) | ~m1_orders_2('#skF_5', '#skF_3', B_200) | B_200='#skF_5' | ~m1_subset_1(B_200, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_651, c_325])).
% 3.95/1.70  tff(c_974, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | ~m1_orders_2('#skF_5', '#skF_3', '#skF_4') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_32, c_967])).
% 3.95/1.70  tff(c_982, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_974])).
% 3.95/1.70  tff(c_984, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_982])).
% 3.95/1.70  tff(c_283, plain, (~m1_orders_2('#skF_4', '#skF_3', k1_xboole_0) | k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_77])).
% 3.95/1.70  tff(c_331, plain, (~m1_orders_2('#skF_4', '#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_283])).
% 3.95/1.70  tff(c_653, plain, (~m1_orders_2('#skF_4', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_651, c_331])).
% 3.95/1.70  tff(c_987, plain, (~m1_orders_2('#skF_4', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_984, c_653])).
% 3.95/1.70  tff(c_996, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_959, c_987])).
% 3.95/1.70  tff(c_998, plain, ('#skF_5'!='#skF_4'), inference(splitRight, [status(thm)], [c_982])).
% 3.95/1.70  tff(c_1050, plain, (![A_8, B_20, C_26]: (m1_subset_1('#skF_2'(A_8, B_20, C_26), u1_struct_0(A_8)) | ~m1_orders_2(C_26, A_8, B_20) | B_20='#skF_5' | ~m1_subset_1(C_26, k1_zfmisc_1(u1_struct_0(A_8))) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_orders_2(A_8) | ~v5_orders_2(A_8) | ~v4_orders_2(A_8) | ~v3_orders_2(A_8) | v2_struct_0(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_651, c_18])).
% 3.95/1.70  tff(c_1053, plain, (![A_219, B_220, C_221]: (k3_orders_2(A_219, B_220, '#skF_2'(A_219, B_220, C_221))=C_221 | ~m1_orders_2(C_221, A_219, B_220) | B_220='#skF_5' | ~m1_subset_1(C_221, k1_zfmisc_1(u1_struct_0(A_219))) | ~m1_subset_1(B_220, k1_zfmisc_1(u1_struct_0(A_219))) | ~l1_orders_2(A_219) | ~v5_orders_2(A_219) | ~v4_orders_2(A_219) | ~v3_orders_2(A_219) | v2_struct_0(A_219))), inference(demodulation, [status(thm), theory('equality')], [c_651, c_14])).
% 3.95/1.70  tff(c_1055, plain, (![B_220]: (k3_orders_2('#skF_3', B_220, '#skF_2'('#skF_3', B_220, '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', B_220) | B_220='#skF_5' | ~m1_subset_1(B_220, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_66, c_1053])).
% 3.95/1.70  tff(c_1063, plain, (![B_220]: (k3_orders_2('#skF_3', B_220, '#skF_2'('#skF_3', B_220, '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', B_220) | B_220='#skF_5' | ~m1_subset_1(B_220, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_1055])).
% 3.95/1.70  tff(c_1087, plain, (![B_226]: (k3_orders_2('#skF_3', B_226, '#skF_2'('#skF_3', B_226, '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', B_226) | B_226='#skF_5' | ~m1_subset_1(B_226, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_1063])).
% 3.95/1.70  tff(c_1094, plain, (k3_orders_2('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))='#skF_5' | ~m1_orders_2('#skF_5', '#skF_3', '#skF_4') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_32, c_1087])).
% 3.95/1.70  tff(c_1102, plain, (k3_orders_2('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))='#skF_5' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1094])).
% 3.95/1.70  tff(c_1103, plain, (k3_orders_2('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_998, c_1102])).
% 3.95/1.70  tff(c_1108, plain, (![B_42]: (r2_hidden(B_42, '#skF_4') | ~r2_hidden(B_42, '#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1(B_42, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1103, c_24])).
% 3.95/1.70  tff(c_1115, plain, (![B_42]: (r2_hidden(B_42, '#skF_4') | ~r2_hidden(B_42, '#skF_5') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1(B_42, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_32, c_1108])).
% 3.95/1.70  tff(c_1116, plain, (![B_42]: (r2_hidden(B_42, '#skF_4') | ~r2_hidden(B_42, '#skF_5') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1(B_42, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_42, c_1115])).
% 3.95/1.70  tff(c_1118, plain, (~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_1116])).
% 3.95/1.70  tff(c_1135, plain, (~m1_orders_2('#skF_5', '#skF_3', '#skF_4') | '#skF_5'='#skF_4' | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1050, c_1118])).
% 3.95/1.70  tff(c_1138, plain, ('#skF_5'='#skF_4' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_32, c_66, c_30, c_1135])).
% 3.95/1.70  tff(c_1140, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_998, c_1138])).
% 3.95/1.70  tff(c_1143, plain, (![B_228]: (r2_hidden(B_228, '#skF_4') | ~r2_hidden(B_228, '#skF_5') | ~m1_subset_1(B_228, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_1116])).
% 3.95/1.70  tff(c_1271, plain, (![B_240, C_241]: (r2_hidden('#skF_1'(u1_struct_0('#skF_3'), B_240, C_241), '#skF_4') | ~r2_hidden('#skF_1'(u1_struct_0('#skF_3'), B_240, C_241), '#skF_5') | r1_tarski(B_240, C_241) | ~m1_subset_1(C_241, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_240, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_6, c_1143])).
% 3.95/1.70  tff(c_1275, plain, (![C_6]: (r2_hidden('#skF_1'(u1_struct_0('#skF_3'), '#skF_5', C_6), '#skF_4') | r1_tarski('#skF_5', C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_4, c_1271])).
% 3.95/1.70  tff(c_1281, plain, (![C_245]: (r2_hidden('#skF_1'(u1_struct_0('#skF_3'), '#skF_5', C_245), '#skF_4') | r1_tarski('#skF_5', C_245) | ~m1_subset_1(C_245, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1275])).
% 3.95/1.70  tff(c_1285, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | r1_tarski('#skF_5', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_1281, c_2])).
% 3.95/1.70  tff(c_1288, plain, (r1_tarski('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_66, c_1285])).
% 3.95/1.70  tff(c_1290, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_1288])).
% 3.95/1.70  tff(c_1291, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_283])).
% 3.95/1.70  tff(c_1313, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1291, c_30, c_1291, c_1291, c_85])).
% 3.95/1.70  tff(c_1317, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1313, c_28])).
% 3.95/1.70  tff(c_1323, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_1317])).
% 3.95/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/1.70  
% 3.95/1.70  Inference rules
% 3.95/1.70  ----------------------
% 3.95/1.70  #Ref     : 0
% 3.95/1.70  #Sup     : 211
% 3.95/1.70  #Fact    : 0
% 3.95/1.70  #Define  : 0
% 3.95/1.70  #Split   : 23
% 3.95/1.70  #Chain   : 0
% 3.95/1.70  #Close   : 0
% 3.95/1.70  
% 3.95/1.70  Ordering : KBO
% 3.95/1.70  
% 3.95/1.70  Simplification rules
% 3.95/1.70  ----------------------
% 3.95/1.70  #Subsume      : 29
% 3.95/1.70  #Demod        : 560
% 3.95/1.70  #Tautology    : 65
% 3.95/1.70  #SimpNegUnit  : 94
% 3.95/1.70  #BackRed      : 54
% 3.95/1.70  
% 3.95/1.70  #Partial instantiations: 0
% 3.95/1.70  #Strategies tried      : 1
% 3.95/1.70  
% 3.95/1.70  Timing (in seconds)
% 3.95/1.70  ----------------------
% 3.95/1.70  Preprocessing        : 0.32
% 3.95/1.70  Parsing              : 0.17
% 3.95/1.70  CNF conversion       : 0.03
% 3.95/1.70  Main loop            : 0.57
% 3.95/1.70  Inferencing          : 0.20
% 3.95/1.70  Reduction            : 0.19
% 3.95/1.70  Demodulation         : 0.13
% 3.95/1.70  BG Simplification    : 0.03
% 3.95/1.70  Subsumption          : 0.12
% 3.95/1.70  Abstraction          : 0.03
% 3.95/1.70  MUC search           : 0.00
% 3.95/1.70  Cooper               : 0.00
% 3.95/1.70  Total                : 0.97
% 3.95/1.70  Index Insertion      : 0.00
% 3.95/1.70  Index Deletion       : 0.00
% 3.95/1.70  Index Matching       : 0.00
% 3.95/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
