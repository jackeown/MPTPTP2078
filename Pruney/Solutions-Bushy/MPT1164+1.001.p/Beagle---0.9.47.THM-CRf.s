%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1164+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:32 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 633 expanded)
%              Number of leaves         :   32 ( 262 expanded)
%              Depth                    :   16
%              Number of atoms          :  329 (2888 expanded)
%              Number of equality atoms :   73 ( 179 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k9_subset_1 > k3_orders_2 > k6_domain_1 > k3_xboole_0 > k2_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_orders_2,type,(
    k2_orders_2: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,negated_conjecture,(
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

tff(f_98,axiom,(
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

tff(f_80,axiom,(
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

tff(f_26,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => k3_orders_2(A,B,C) = k9_subset_1(u1_struct_0(A),k2_orders_2(A,k6_domain_1(u1_struct_0(A),C)),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_orders_2)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_104,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_106,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_28,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_38,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_36,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_34,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_32,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_178,plain,(
    ! [C_60,A_61,B_62] :
      ( m1_subset_1(C_60,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ m1_orders_2(C_60,A_61,B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_orders_2(A_61)
      | ~ v5_orders_2(A_61)
      | ~ v4_orders_2(A_61)
      | ~ v3_orders_2(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_180,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_178])).

tff(c_183,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_180])).

tff(c_184,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_183])).

tff(c_210,plain,(
    ! [A_66,B_67,C_68] :
      ( r2_hidden('#skF_1'(A_66,B_67,C_68),B_67)
      | ~ m1_orders_2(C_68,A_66,B_67)
      | k1_xboole_0 = B_67
      | ~ m1_subset_1(C_68,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_orders_2(A_66)
      | ~ v5_orders_2(A_66)
      | ~ v4_orders_2(A_66)
      | ~ v3_orders_2(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_212,plain,(
    ! [B_67] :
      ( r2_hidden('#skF_1'('#skF_2',B_67,'#skF_4'),B_67)
      | ~ m1_orders_2('#skF_4','#skF_2',B_67)
      | k1_xboole_0 = B_67
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_184,c_210])).

tff(c_217,plain,(
    ! [B_67] :
      ( r2_hidden('#skF_1'('#skF_2',B_67,'#skF_4'),B_67)
      | ~ m1_orders_2('#skF_4','#skF_2',B_67)
      | k1_xboole_0 = B_67
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_212])).

tff(c_537,plain,(
    ! [B_106] :
      ( r2_hidden('#skF_1'('#skF_2',B_106,'#skF_4'),B_106)
      | ~ m1_orders_2('#skF_4','#skF_2',B_106)
      | k1_xboole_0 = B_106
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_217])).

tff(c_543,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | ~ m1_orders_2('#skF_4','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_30,c_537])).

tff(c_548,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_543])).

tff(c_549,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_548])).

tff(c_233,plain,(
    ! [B_70] :
      ( r2_hidden('#skF_1'('#skF_2',B_70,'#skF_4'),B_70)
      | ~ m1_orders_2('#skF_4','#skF_2',B_70)
      | k1_xboole_0 = B_70
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_217])).

tff(c_237,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | ~ m1_orders_2('#skF_4','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_30,c_233])).

tff(c_241,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_237])).

tff(c_243,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_241])).

tff(c_197,plain,(
    ! [C_64,A_65] :
      ( k1_xboole_0 = C_64
      | ~ m1_orders_2(C_64,A_65,k1_xboole_0)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_orders_2(A_65)
      | ~ v5_orders_2(A_65)
      | ~ v4_orders_2(A_65)
      | ~ v3_orders_2(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_201,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ m1_orders_2('#skF_3','#skF_2',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_197])).

tff(c_208,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ m1_orders_2('#skF_3','#skF_2',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_201])).

tff(c_209,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ m1_orders_2('#skF_3','#skF_2',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_208])).

tff(c_223,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_209])).

tff(c_247,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_223])).

tff(c_256,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_247])).

tff(c_258,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_241])).

tff(c_16,plain,(
    ! [A_10,B_22,C_28] :
      ( m1_subset_1('#skF_1'(A_10,B_22,C_28),u1_struct_0(A_10))
      | ~ m1_orders_2(C_28,A_10,B_22)
      | k1_xboole_0 = B_22
      | ~ m1_subset_1(C_28,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_orders_2(A_10)
      | ~ v5_orders_2(A_10)
      | ~ v4_orders_2(A_10)
      | ~ v3_orders_2(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_26,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_313,plain,(
    ! [A_79,B_80,C_81] :
      ( k3_orders_2(A_79,B_80,'#skF_1'(A_79,B_80,C_81)) = C_81
      | ~ m1_orders_2(C_81,A_79,B_80)
      | k1_xboole_0 = B_80
      | ~ m1_subset_1(C_81,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_orders_2(A_79)
      | ~ v5_orders_2(A_79)
      | ~ v4_orders_2(A_79)
      | ~ v3_orders_2(A_79)
      | v2_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_315,plain,(
    ! [B_80] :
      ( k3_orders_2('#skF_2',B_80,'#skF_1'('#skF_2',B_80,'#skF_4')) = '#skF_4'
      | ~ m1_orders_2('#skF_4','#skF_2',B_80)
      | k1_xboole_0 = B_80
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_184,c_313])).

tff(c_320,plain,(
    ! [B_80] :
      ( k3_orders_2('#skF_2',B_80,'#skF_1'('#skF_2',B_80,'#skF_4')) = '#skF_4'
      | ~ m1_orders_2('#skF_4','#skF_2',B_80)
      | k1_xboole_0 = B_80
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_315])).

tff(c_352,plain,(
    ! [B_87] :
      ( k3_orders_2('#skF_2',B_87,'#skF_1'('#skF_2',B_87,'#skF_4')) = '#skF_4'
      | ~ m1_orders_2('#skF_4','#skF_2',B_87)
      | k1_xboole_0 = B_87
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_320])).

tff(c_356,plain,
    ( k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4')) = '#skF_4'
    | ~ m1_orders_2('#skF_4','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_30,c_352])).

tff(c_360,plain,
    ( k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_356])).

tff(c_361,plain,(
    k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_258,c_360])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_260,plain,(
    ! [A_74,C_75,B_76] :
      ( k9_subset_1(u1_struct_0(A_74),k2_orders_2(A_74,k6_domain_1(u1_struct_0(A_74),C_75)),B_76) = k3_orders_2(A_74,B_76,C_75)
      | ~ m1_subset_1(C_75,u1_struct_0(A_74))
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_orders_2(A_74)
      | ~ v5_orders_2(A_74)
      | ~ v4_orders_2(A_74)
      | ~ v3_orders_2(A_74)
      | v2_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_145,plain,(
    ! [A_53,B_54,C_55] :
      ( k9_subset_1(A_53,B_54,C_55) = k3_xboole_0(B_54,C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_148,plain,(
    ! [B_54] : k9_subset_1(u1_struct_0('#skF_2'),B_54,'#skF_3') = k3_xboole_0(B_54,'#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_145])).

tff(c_271,plain,(
    ! [C_75] :
      ( k3_xboole_0(k2_orders_2('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_75)),'#skF_3') = k3_orders_2('#skF_2','#skF_3',C_75)
      | ~ m1_subset_1(C_75,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_148])).

tff(c_288,plain,(
    ! [C_75] :
      ( k3_xboole_0('#skF_3',k2_orders_2('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_75))) = k3_orders_2('#skF_2','#skF_3',C_75)
      | ~ m1_subset_1(C_75,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_2,c_271])).

tff(c_297,plain,(
    ! [C_77] :
      ( k3_xboole_0('#skF_3',k2_orders_2('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_77))) = k3_orders_2('#skF_2','#skF_3',C_77)
      | ~ m1_subset_1(C_77,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_288])).

tff(c_22,plain,(
    ! [A_39,B_40] : r1_tarski(k3_xboole_0(A_39,B_40),A_39) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_306,plain,(
    ! [C_77] :
      ( r1_tarski(k3_orders_2('#skF_2','#skF_3',C_77),'#skF_3')
      | ~ m1_subset_1(C_77,u1_struct_0('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_297,c_22])).

tff(c_368,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_361,c_306])).

tff(c_371,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_368])).

tff(c_381,plain,
    ( ~ m1_orders_2('#skF_4','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_371])).

tff(c_384,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_184,c_28,c_381])).

tff(c_386,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_258,c_384])).

tff(c_388,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_199,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_orders_2('#skF_4','#skF_2',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_184,c_197])).

tff(c_204,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_orders_2('#skF_4','#skF_2',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_199])).

tff(c_205,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_orders_2('#skF_4','#skF_2',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_204])).

tff(c_420,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_orders_2('#skF_4','#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_205])).

tff(c_421,plain,(
    ~ m1_orders_2('#skF_4','#skF_2',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_420])).

tff(c_556,plain,(
    ~ m1_orders_2('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_549,c_421])).

tff(c_567,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_556])).

tff(c_569,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_548])).

tff(c_570,plain,(
    ! [A_107,B_108,C_109] :
      ( k3_orders_2(A_107,B_108,'#skF_1'(A_107,B_108,C_109)) = C_109
      | ~ m1_orders_2(C_109,A_107,B_108)
      | k1_xboole_0 = B_108
      | ~ m1_subset_1(C_109,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_orders_2(A_107)
      | ~ v5_orders_2(A_107)
      | ~ v4_orders_2(A_107)
      | ~ v3_orders_2(A_107)
      | v2_struct_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_574,plain,(
    ! [B_108] :
      ( k3_orders_2('#skF_2',B_108,'#skF_1'('#skF_2',B_108,'#skF_4')) = '#skF_4'
      | ~ m1_orders_2('#skF_4','#skF_2',B_108)
      | k1_xboole_0 = B_108
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_184,c_570])).

tff(c_583,plain,(
    ! [B_108] :
      ( k3_orders_2('#skF_2',B_108,'#skF_1'('#skF_2',B_108,'#skF_4')) = '#skF_4'
      | ~ m1_orders_2('#skF_4','#skF_2',B_108)
      | k1_xboole_0 = B_108
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_574])).

tff(c_619,plain,(
    ! [B_115] :
      ( k3_orders_2('#skF_2',B_115,'#skF_1'('#skF_2',B_115,'#skF_4')) = '#skF_4'
      | ~ m1_orders_2('#skF_4','#skF_2',B_115)
      | k1_xboole_0 = B_115
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_583])).

tff(c_625,plain,
    ( k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4')) = '#skF_4'
    | ~ m1_orders_2('#skF_4','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_30,c_619])).

tff(c_630,plain,
    ( k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_625])).

tff(c_631,plain,(
    k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_569,c_630])).

tff(c_440,plain,(
    ! [A_93,C_94,B_95] :
      ( k9_subset_1(u1_struct_0(A_93),k2_orders_2(A_93,k6_domain_1(u1_struct_0(A_93),C_94)),B_95) = k3_orders_2(A_93,B_95,C_94)
      | ~ m1_subset_1(C_94,u1_struct_0(A_93))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_orders_2(A_93)
      | ~ v5_orders_2(A_93)
      | ~ v4_orders_2(A_93)
      | ~ v3_orders_2(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_455,plain,(
    ! [C_94] :
      ( k3_xboole_0(k2_orders_2('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_94)),'#skF_3') = k3_orders_2('#skF_2','#skF_3',C_94)
      | ~ m1_subset_1(C_94,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_440,c_148])).

tff(c_479,plain,(
    ! [C_94] :
      ( k3_xboole_0('#skF_3',k2_orders_2('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_94))) = k3_orders_2('#skF_2','#skF_3',C_94)
      | ~ m1_subset_1(C_94,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_2,c_455])).

tff(c_494,plain,(
    ! [C_97] :
      ( k3_xboole_0('#skF_3',k2_orders_2('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_97))) = k3_orders_2('#skF_2','#skF_3',C_97)
      | ~ m1_subset_1(C_97,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_479])).

tff(c_503,plain,(
    ! [C_97] :
      ( r1_tarski(k3_orders_2('#skF_2','#skF_3',C_97),'#skF_3')
      | ~ m1_subset_1(C_97,u1_struct_0('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_22])).

tff(c_640,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_631,c_503])).

tff(c_646,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_640])).

tff(c_650,plain,
    ( ~ m1_orders_2('#skF_4','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_646])).

tff(c_653,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_184,c_28,c_650])).

tff(c_655,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_569,c_653])).

tff(c_656,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_420])).

tff(c_24,plain,(
    ! [A_41] : k3_xboole_0(A_41,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_48,plain,(
    ! [A_47,B_48] : r1_tarski(k3_xboole_0(A_47,B_48),A_47) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_51,plain,(
    ! [A_41] : r1_tarski(k1_xboole_0,A_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_48])).

tff(c_676,plain,(
    ! [A_41] : r1_tarski('#skF_4',A_41) ),
    inference(demodulation,[status(thm),theory(equality)],[c_656,c_51])).

tff(c_685,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_676,c_26])).

%------------------------------------------------------------------------------
