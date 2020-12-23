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
% DateTime   : Thu Dec  3 10:20:02 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 262 expanded)
%              Number of leaves         :   36 ( 113 expanded)
%              Depth                    :   10
%              Number of atoms          :  281 (1163 expanded)
%              Number of equality atoms :   17 (  31 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k1_orders_1,type,(
    k1_orders_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(m1_orders_2,type,(
    m1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_201,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
           => ! [C] :
                ( m2_orders_2(C,A,B)
               => ! [D] :
                    ( m2_orders_2(D,A,B)
                   => ( r2_xboole_0(C,D)
                    <=> m1_orders_2(C,A,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_orders_2)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ! [C] :
          ( m2_orders_2(C,A,B)
         => ( v6_orders_2(C,A)
            & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_orders_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_104,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_orders_2)).

tff(f_129,axiom,(
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
             => ~ ( B != k1_xboole_0
                  & m1_orders_2(B,A,C)
                  & m1_orders_2(C,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_orders_2)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_148,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( m2_orders_2(C,A,B)
             => r2_hidden(k1_funct_1(B,u1_struct_0(A)),C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_orders_2)).

tff(f_47,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : ~ r2_xboole_0(A,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

tff(f_176,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( m2_orders_2(C,A,B)
             => ! [D] :
                  ( m2_orders_2(D,A,B)
                 => ( C != D
                   => ( m1_orders_2(C,A,D)
                    <=> ~ m1_orders_2(D,A,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_orders_2)).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_32,plain,(
    m2_orders_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_44,plain,(
    v3_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_42,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_40,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_38,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_36,plain,(
    m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_183,plain,(
    ! [C_102,A_103,B_104] :
      ( m1_subset_1(C_102,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ m2_orders_2(C_102,A_103,B_104)
      | ~ m1_orders_1(B_104,k1_orders_1(u1_struct_0(A_103)))
      | ~ l1_orders_2(A_103)
      | ~ v5_orders_2(A_103)
      | ~ v4_orders_2(A_103)
      | ~ v3_orders_2(A_103)
      | v2_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_185,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_183])).

tff(c_188,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_36,c_185])).

tff(c_189,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_188])).

tff(c_62,plain,(
    ! [A_73,B_74] :
      ( r2_xboole_0(A_73,B_74)
      | B_74 = A_73
      | ~ r1_tarski(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_48,plain,
    ( ~ m1_orders_2('#skF_3','#skF_1','#skF_4')
    | ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_60,plain,(
    ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_76,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_60])).

tff(c_81,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_54,plain,
    ( r2_xboole_0('#skF_3','#skF_4')
    | m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_61,plain,(
    m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54])).

tff(c_82,plain,(
    ! [C_75,B_76,A_77] :
      ( r1_tarski(C_75,B_76)
      | ~ m1_orders_2(C_75,A_77,B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_orders_2(A_77)
      | ~ v5_orders_2(A_77)
      | ~ v4_orders_2(A_77)
      | ~ v3_orders_2(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_84,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_61,c_82])).

tff(c_87,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_84])).

tff(c_88,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_81,c_87])).

tff(c_120,plain,(
    ! [C_87,A_88,B_89] :
      ( m1_subset_1(C_87,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ m2_orders_2(C_87,A_88,B_89)
      | ~ m1_orders_1(B_89,k1_orders_1(u1_struct_0(A_88)))
      | ~ l1_orders_2(A_88)
      | ~ v5_orders_2(A_88)
      | ~ v4_orders_2(A_88)
      | ~ v3_orders_2(A_88)
      | v2_struct_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_124,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_120])).

tff(c_131,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_36,c_124])).

tff(c_133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_88,c_131])).

tff(c_134,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_136,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_61])).

tff(c_209,plain,(
    ! [C_113,A_114,B_115] :
      ( ~ m1_orders_2(C_113,A_114,B_115)
      | ~ m1_orders_2(B_115,A_114,C_113)
      | k1_xboole_0 = B_115
      | ~ m1_subset_1(C_113,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_orders_2(A_114)
      | ~ v5_orders_2(A_114)
      | ~ v4_orders_2(A_114)
      | ~ v3_orders_2(A_114)
      | v2_struct_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_211,plain,
    ( ~ m1_orders_2('#skF_4','#skF_1','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_136,c_209])).

tff(c_214,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_189,c_136,c_211])).

tff(c_215,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_214])).

tff(c_10,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_190,plain,(
    ! [B_105,A_106,C_107] :
      ( r2_hidden(k1_funct_1(B_105,u1_struct_0(A_106)),C_107)
      | ~ m2_orders_2(C_107,A_106,B_105)
      | ~ m1_orders_1(B_105,k1_orders_1(u1_struct_0(A_106)))
      | ~ l1_orders_2(A_106)
      | ~ v5_orders_2(A_106)
      | ~ v4_orders_2(A_106)
      | ~ v3_orders_2(A_106)
      | v2_struct_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_14,plain,(
    ! [B_9,A_8] :
      ( ~ r1_tarski(B_9,A_8)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_195,plain,(
    ! [C_108,B_109,A_110] :
      ( ~ r1_tarski(C_108,k1_funct_1(B_109,u1_struct_0(A_110)))
      | ~ m2_orders_2(C_108,A_110,B_109)
      | ~ m1_orders_1(B_109,k1_orders_1(u1_struct_0(A_110)))
      | ~ l1_orders_2(A_110)
      | ~ v5_orders_2(A_110)
      | ~ v4_orders_2(A_110)
      | ~ v3_orders_2(A_110)
      | v2_struct_0(A_110) ) ),
    inference(resolution,[status(thm)],[c_190,c_14])).

tff(c_201,plain,(
    ! [A_111,B_112] :
      ( ~ m2_orders_2(k1_xboole_0,A_111,B_112)
      | ~ m1_orders_1(B_112,k1_orders_1(u1_struct_0(A_111)))
      | ~ l1_orders_2(A_111)
      | ~ v5_orders_2(A_111)
      | ~ v4_orders_2(A_111)
      | ~ v3_orders_2(A_111)
      | v2_struct_0(A_111) ) ),
    inference(resolution,[status(thm)],[c_10,c_195])).

tff(c_204,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_1','#skF_2')
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_201])).

tff(c_207,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_204])).

tff(c_208,plain,(
    ~ m2_orders_2(k1_xboole_0,'#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_207])).

tff(c_217,plain,(
    ~ m2_orders_2('#skF_4','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_208])).

tff(c_223,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_217])).

tff(c_225,plain,(
    r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( ~ r2_xboole_0(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_233,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_225,c_12])).

tff(c_34,plain,(
    m2_orders_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_280,plain,(
    ! [C_130,A_131,B_132] :
      ( m1_subset_1(C_130,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ m2_orders_2(C_130,A_131,B_132)
      | ~ m1_orders_1(B_132,k1_orders_1(u1_struct_0(A_131)))
      | ~ l1_orders_2(A_131)
      | ~ v5_orders_2(A_131)
      | ~ v4_orders_2(A_131)
      | ~ v3_orders_2(A_131)
      | v2_struct_0(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_282,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_280])).

tff(c_287,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_36,c_282])).

tff(c_288,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_287])).

tff(c_8,plain,(
    ! [A_3] : ~ r2_xboole_0(A_3,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_224,plain,(
    ~ m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_313,plain,(
    ! [C_144,A_145,D_146,B_147] :
      ( m1_orders_2(C_144,A_145,D_146)
      | m1_orders_2(D_146,A_145,C_144)
      | D_146 = C_144
      | ~ m2_orders_2(D_146,A_145,B_147)
      | ~ m2_orders_2(C_144,A_145,B_147)
      | ~ m1_orders_1(B_147,k1_orders_1(u1_struct_0(A_145)))
      | ~ l1_orders_2(A_145)
      | ~ v5_orders_2(A_145)
      | ~ v4_orders_2(A_145)
      | ~ v3_orders_2(A_145)
      | v2_struct_0(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_315,plain,(
    ! [C_144] :
      ( m1_orders_2(C_144,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_144)
      | C_144 = '#skF_3'
      | ~ m2_orders_2(C_144,'#skF_1','#skF_2')
      | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
      | ~ l1_orders_2('#skF_1')
      | ~ v5_orders_2('#skF_1')
      | ~ v4_orders_2('#skF_1')
      | ~ v3_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_313])).

tff(c_320,plain,(
    ! [C_144] :
      ( m1_orders_2(C_144,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_144)
      | C_144 = '#skF_3'
      | ~ m2_orders_2(C_144,'#skF_1','#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_36,c_315])).

tff(c_326,plain,(
    ! [C_148] :
      ( m1_orders_2(C_148,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_148)
      | C_148 = '#skF_3'
      | ~ m2_orders_2(C_148,'#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_320])).

tff(c_332,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | m1_orders_2('#skF_3','#skF_1','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32,c_326])).

tff(c_337,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_332])).

tff(c_338,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_337])).

tff(c_357,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_225])).

tff(c_362,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_357])).

tff(c_363,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_337])).

tff(c_22,plain,(
    ! [C_24,B_22,A_18] :
      ( r1_tarski(C_24,B_22)
      | ~ m1_orders_2(C_24,A_18,B_22)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_orders_2(A_18)
      | ~ v5_orders_2(A_18)
      | ~ v4_orders_2(A_18)
      | ~ v3_orders_2(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_370,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_363,c_22])).

tff(c_381,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_288,c_370])).

tff(c_383,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_233,c_381])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:53:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.59/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.35  
% 2.59/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.35  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.59/1.35  
% 2.59/1.35  %Foreground sorts:
% 2.59/1.35  
% 2.59/1.35  
% 2.59/1.35  %Background operators:
% 2.59/1.35  
% 2.59/1.35  
% 2.59/1.35  %Foreground operators:
% 2.59/1.35  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.59/1.35  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.59/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.59/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.59/1.35  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.59/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.59/1.35  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.59/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.59/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.59/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.59/1.35  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.59/1.35  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.59/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.59/1.35  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.59/1.35  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.59/1.35  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.59/1.35  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.59/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.35  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 2.59/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.59/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.35  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.59/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.59/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.59/1.35  
% 2.59/1.37  tff(f_201, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_orders_2)).
% 2.59/1.37  tff(f_85, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 2.59/1.37  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.59/1.37  tff(f_104, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_orders_2)).
% 2.59/1.37  tff(f_129, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_orders_2)).
% 2.59/1.37  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.59/1.37  tff(f_148, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_orders_2)).
% 2.59/1.37  tff(f_47, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.59/1.37  tff(f_42, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_xboole_1)).
% 2.59/1.37  tff(f_35, axiom, (![A, B]: ~r2_xboole_0(A, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 2.59/1.37  tff(f_176, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_orders_2)).
% 2.59/1.37  tff(c_46, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_201])).
% 2.59/1.37  tff(c_32, plain, (m2_orders_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_201])).
% 2.59/1.37  tff(c_44, plain, (v3_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_201])).
% 2.59/1.37  tff(c_42, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_201])).
% 2.59/1.37  tff(c_40, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_201])).
% 2.59/1.37  tff(c_38, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_201])).
% 2.59/1.37  tff(c_36, plain, (m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_201])).
% 2.59/1.37  tff(c_183, plain, (![C_102, A_103, B_104]: (m1_subset_1(C_102, k1_zfmisc_1(u1_struct_0(A_103))) | ~m2_orders_2(C_102, A_103, B_104) | ~m1_orders_1(B_104, k1_orders_1(u1_struct_0(A_103))) | ~l1_orders_2(A_103) | ~v5_orders_2(A_103) | ~v4_orders_2(A_103) | ~v3_orders_2(A_103) | v2_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.59/1.37  tff(c_185, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_183])).
% 2.59/1.37  tff(c_188, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_36, c_185])).
% 2.59/1.37  tff(c_189, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_46, c_188])).
% 2.59/1.37  tff(c_62, plain, (![A_73, B_74]: (r2_xboole_0(A_73, B_74) | B_74=A_73 | ~r1_tarski(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.59/1.37  tff(c_48, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4') | ~r2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_201])).
% 2.59/1.37  tff(c_60, plain, (~r2_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_48])).
% 2.59/1.37  tff(c_76, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_62, c_60])).
% 2.59/1.37  tff(c_81, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_76])).
% 2.59/1.37  tff(c_54, plain, (r2_xboole_0('#skF_3', '#skF_4') | m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_201])).
% 2.59/1.37  tff(c_61, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_60, c_54])).
% 2.59/1.37  tff(c_82, plain, (![C_75, B_76, A_77]: (r1_tarski(C_75, B_76) | ~m1_orders_2(C_75, A_77, B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_orders_2(A_77) | ~v5_orders_2(A_77) | ~v4_orders_2(A_77) | ~v3_orders_2(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.59/1.37  tff(c_84, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_61, c_82])).
% 2.59/1.37  tff(c_87, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_84])).
% 2.59/1.37  tff(c_88, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_46, c_81, c_87])).
% 2.59/1.37  tff(c_120, plain, (![C_87, A_88, B_89]: (m1_subset_1(C_87, k1_zfmisc_1(u1_struct_0(A_88))) | ~m2_orders_2(C_87, A_88, B_89) | ~m1_orders_1(B_89, k1_orders_1(u1_struct_0(A_88))) | ~l1_orders_2(A_88) | ~v5_orders_2(A_88) | ~v4_orders_2(A_88) | ~v3_orders_2(A_88) | v2_struct_0(A_88))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.59/1.37  tff(c_124, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_120])).
% 2.59/1.37  tff(c_131, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_36, c_124])).
% 2.59/1.37  tff(c_133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_88, c_131])).
% 2.59/1.37  tff(c_134, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_76])).
% 2.59/1.37  tff(c_136, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_61])).
% 2.59/1.37  tff(c_209, plain, (![C_113, A_114, B_115]: (~m1_orders_2(C_113, A_114, B_115) | ~m1_orders_2(B_115, A_114, C_113) | k1_xboole_0=B_115 | ~m1_subset_1(C_113, k1_zfmisc_1(u1_struct_0(A_114))) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_orders_2(A_114) | ~v5_orders_2(A_114) | ~v4_orders_2(A_114) | ~v3_orders_2(A_114) | v2_struct_0(A_114))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.59/1.37  tff(c_211, plain, (~m1_orders_2('#skF_4', '#skF_1', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_136, c_209])).
% 2.59/1.37  tff(c_214, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_189, c_136, c_211])).
% 2.59/1.37  tff(c_215, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_46, c_214])).
% 2.59/1.37  tff(c_10, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.59/1.37  tff(c_190, plain, (![B_105, A_106, C_107]: (r2_hidden(k1_funct_1(B_105, u1_struct_0(A_106)), C_107) | ~m2_orders_2(C_107, A_106, B_105) | ~m1_orders_1(B_105, k1_orders_1(u1_struct_0(A_106))) | ~l1_orders_2(A_106) | ~v5_orders_2(A_106) | ~v4_orders_2(A_106) | ~v3_orders_2(A_106) | v2_struct_0(A_106))), inference(cnfTransformation, [status(thm)], [f_148])).
% 2.59/1.37  tff(c_14, plain, (![B_9, A_8]: (~r1_tarski(B_9, A_8) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.59/1.37  tff(c_195, plain, (![C_108, B_109, A_110]: (~r1_tarski(C_108, k1_funct_1(B_109, u1_struct_0(A_110))) | ~m2_orders_2(C_108, A_110, B_109) | ~m1_orders_1(B_109, k1_orders_1(u1_struct_0(A_110))) | ~l1_orders_2(A_110) | ~v5_orders_2(A_110) | ~v4_orders_2(A_110) | ~v3_orders_2(A_110) | v2_struct_0(A_110))), inference(resolution, [status(thm)], [c_190, c_14])).
% 2.59/1.37  tff(c_201, plain, (![A_111, B_112]: (~m2_orders_2(k1_xboole_0, A_111, B_112) | ~m1_orders_1(B_112, k1_orders_1(u1_struct_0(A_111))) | ~l1_orders_2(A_111) | ~v5_orders_2(A_111) | ~v4_orders_2(A_111) | ~v3_orders_2(A_111) | v2_struct_0(A_111))), inference(resolution, [status(thm)], [c_10, c_195])).
% 2.59/1.37  tff(c_204, plain, (~m2_orders_2(k1_xboole_0, '#skF_1', '#skF_2') | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_201])).
% 2.59/1.37  tff(c_207, plain, (~m2_orders_2(k1_xboole_0, '#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_204])).
% 2.59/1.37  tff(c_208, plain, (~m2_orders_2(k1_xboole_0, '#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_46, c_207])).
% 2.59/1.37  tff(c_217, plain, (~m2_orders_2('#skF_4', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_215, c_208])).
% 2.59/1.37  tff(c_223, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_217])).
% 2.59/1.37  tff(c_225, plain, (r2_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_48])).
% 2.59/1.37  tff(c_12, plain, (![B_7, A_6]: (~r2_xboole_0(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.59/1.37  tff(c_233, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_225, c_12])).
% 2.59/1.37  tff(c_34, plain, (m2_orders_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_201])).
% 2.59/1.37  tff(c_280, plain, (![C_130, A_131, B_132]: (m1_subset_1(C_130, k1_zfmisc_1(u1_struct_0(A_131))) | ~m2_orders_2(C_130, A_131, B_132) | ~m1_orders_1(B_132, k1_orders_1(u1_struct_0(A_131))) | ~l1_orders_2(A_131) | ~v5_orders_2(A_131) | ~v4_orders_2(A_131) | ~v3_orders_2(A_131) | v2_struct_0(A_131))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.59/1.37  tff(c_282, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_280])).
% 2.59/1.37  tff(c_287, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_36, c_282])).
% 2.59/1.37  tff(c_288, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_46, c_287])).
% 2.59/1.37  tff(c_8, plain, (![A_3]: (~r2_xboole_0(A_3, A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.59/1.37  tff(c_224, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(splitRight, [status(thm)], [c_48])).
% 2.59/1.37  tff(c_313, plain, (![C_144, A_145, D_146, B_147]: (m1_orders_2(C_144, A_145, D_146) | m1_orders_2(D_146, A_145, C_144) | D_146=C_144 | ~m2_orders_2(D_146, A_145, B_147) | ~m2_orders_2(C_144, A_145, B_147) | ~m1_orders_1(B_147, k1_orders_1(u1_struct_0(A_145))) | ~l1_orders_2(A_145) | ~v5_orders_2(A_145) | ~v4_orders_2(A_145) | ~v3_orders_2(A_145) | v2_struct_0(A_145))), inference(cnfTransformation, [status(thm)], [f_176])).
% 2.59/1.37  tff(c_315, plain, (![C_144]: (m1_orders_2(C_144, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_144) | C_144='#skF_3' | ~m2_orders_2(C_144, '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_313])).
% 2.59/1.37  tff(c_320, plain, (![C_144]: (m1_orders_2(C_144, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_144) | C_144='#skF_3' | ~m2_orders_2(C_144, '#skF_1', '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_36, c_315])).
% 2.59/1.37  tff(c_326, plain, (![C_148]: (m1_orders_2(C_148, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_148) | C_148='#skF_3' | ~m2_orders_2(C_148, '#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_46, c_320])).
% 2.59/1.37  tff(c_332, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', '#skF_4') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_32, c_326])).
% 2.59/1.37  tff(c_337, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_224, c_332])).
% 2.59/1.37  tff(c_338, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_337])).
% 2.59/1.37  tff(c_357, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_338, c_225])).
% 2.59/1.37  tff(c_362, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_357])).
% 2.59/1.37  tff(c_363, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_337])).
% 2.59/1.37  tff(c_22, plain, (![C_24, B_22, A_18]: (r1_tarski(C_24, B_22) | ~m1_orders_2(C_24, A_18, B_22) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_orders_2(A_18) | ~v5_orders_2(A_18) | ~v4_orders_2(A_18) | ~v3_orders_2(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.59/1.37  tff(c_370, plain, (r1_tarski('#skF_4', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_363, c_22])).
% 2.59/1.37  tff(c_381, plain, (r1_tarski('#skF_4', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_288, c_370])).
% 2.59/1.37  tff(c_383, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_233, c_381])).
% 2.59/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.37  
% 2.59/1.37  Inference rules
% 2.59/1.37  ----------------------
% 2.59/1.37  #Ref     : 0
% 2.59/1.37  #Sup     : 49
% 2.59/1.37  #Fact    : 0
% 2.59/1.37  #Define  : 0
% 2.59/1.37  #Split   : 3
% 2.59/1.37  #Chain   : 0
% 2.59/1.37  #Close   : 0
% 2.59/1.37  
% 2.59/1.37  Ordering : KBO
% 2.59/1.37  
% 2.59/1.37  Simplification rules
% 2.59/1.37  ----------------------
% 2.59/1.37  #Subsume      : 6
% 2.59/1.37  #Demod        : 134
% 2.59/1.37  #Tautology    : 21
% 2.59/1.37  #SimpNegUnit  : 27
% 2.59/1.37  #BackRed      : 16
% 2.59/1.37  
% 2.59/1.37  #Partial instantiations: 0
% 2.59/1.37  #Strategies tried      : 1
% 2.59/1.37  
% 2.59/1.37  Timing (in seconds)
% 2.59/1.37  ----------------------
% 2.76/1.37  Preprocessing        : 0.32
% 2.76/1.37  Parsing              : 0.18
% 2.76/1.37  CNF conversion       : 0.03
% 2.76/1.37  Main loop            : 0.25
% 2.76/1.37  Inferencing          : 0.10
% 2.76/1.37  Reduction            : 0.08
% 2.76/1.37  Demodulation         : 0.05
% 2.76/1.37  BG Simplification    : 0.02
% 2.76/1.37  Subsumption          : 0.04
% 2.76/1.37  Abstraction          : 0.01
% 2.76/1.37  MUC search           : 0.00
% 2.76/1.37  Cooper               : 0.00
% 2.76/1.37  Total                : 0.62
% 2.76/1.37  Index Insertion      : 0.00
% 2.76/1.37  Index Deletion       : 0.00
% 2.76/1.37  Index Matching       : 0.00
% 2.76/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
