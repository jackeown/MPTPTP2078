%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:16 EST 2020

% Result     : Theorem 4.13s
% Output     : CNFRefutation 4.41s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 323 expanded)
%              Number of leaves         :   38 ( 125 expanded)
%              Depth                    :   13
%              Number of atoms          :  210 ( 961 expanded)
%              Number of equality atoms :   58 ( 227 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_136,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ! [E] :
                  ( m1_subset_1(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_funct_2)).

tff(f_87,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k1_relat_1(A) = k1_relat_1(B)
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_226,plain,(
    ! [C_77,B_78,A_79] :
      ( v1_xboole_0(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(B_78,A_79)))
      | ~ v1_xboole_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_242,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_226])).

tff(c_246,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_242])).

tff(c_6,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1184,plain,(
    ! [A_189,B_190,C_191,D_192] :
      ( r2_relset_1(A_189,B_190,C_191,C_191)
      | ~ m1_subset_1(D_192,k1_zfmisc_1(k2_zfmisc_1(A_189,B_190)))
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_189,B_190))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1200,plain,(
    ! [A_195,B_196,C_197] :
      ( r2_relset_1(A_195,B_196,C_197,C_197)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(A_195,B_196))) ) ),
    inference(resolution,[status(thm)],[c_6,c_1184])).

tff(c_1212,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_1200])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_94,plain,(
    ! [C_52,A_53,B_54] :
      ( v1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_111,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_94])).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_52,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_284,plain,(
    ! [A_93,B_94,C_95] :
      ( k1_relset_1(A_93,B_94,C_95) = k1_relat_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_301,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_284])).

tff(c_1042,plain,(
    ! [B_177,A_178,C_179] :
      ( k1_xboole_0 = B_177
      | k1_relset_1(A_178,B_177,C_179) = A_178
      | ~ v1_funct_2(C_179,A_178,B_177)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_178,B_177))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1052,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_1042])).

tff(c_1063,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_301,c_1052])).

tff(c_1072,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1063])).

tff(c_110,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_94])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_58,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_300,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_284])).

tff(c_1049,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_1042])).

tff(c_1060,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_300,c_1049])).

tff(c_1088,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1060])).

tff(c_162,plain,(
    ! [C_67,A_68,B_69] :
      ( v4_relat_1(C_67,A_68)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_179,plain,(
    v4_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_162])).

tff(c_16,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k1_relat_1(B_10),A_9)
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1080,plain,(
    ! [A_9] :
      ( r1_tarski('#skF_2',A_9)
      | ~ v4_relat_1('#skF_5',A_9)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1072,c_16])).

tff(c_1148,plain,(
    ! [A_186] :
      ( r1_tarski('#skF_2',A_186)
      | ~ v4_relat_1('#skF_5',A_186) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_1080])).

tff(c_1152,plain,(
    r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_179,c_1148])).

tff(c_1250,plain,(
    ! [A_205,B_206] :
      ( r2_hidden('#skF_1'(A_205,B_206),k1_relat_1(A_205))
      | B_206 = A_205
      | k1_relat_1(B_206) != k1_relat_1(A_205)
      | ~ v1_funct_1(B_206)
      | ~ v1_relat_1(B_206)
      | ~ v1_funct_1(A_205)
      | ~ v1_relat_1(A_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1255,plain,(
    ! [B_206] :
      ( r2_hidden('#skF_1'('#skF_4',B_206),'#skF_2')
      | B_206 = '#skF_4'
      | k1_relat_1(B_206) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_206)
      | ~ v1_relat_1(B_206)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1088,c_1250])).

tff(c_1321,plain,(
    ! [B_215] :
      ( r2_hidden('#skF_1'('#skF_4',B_215),'#skF_2')
      | B_215 = '#skF_4'
      | k1_relat_1(B_215) != '#skF_2'
      | ~ v1_funct_1(B_215)
      | ~ v1_relat_1(B_215) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_60,c_1088,c_1255])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_247,plain,(
    ! [A_80,C_81,B_82] :
      ( m1_subset_1(A_80,C_81)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(C_81))
      | ~ r2_hidden(A_80,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_256,plain,(
    ! [A_80,B_5,A_4] :
      ( m1_subset_1(A_80,B_5)
      | ~ r2_hidden(A_80,A_4)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(resolution,[status(thm)],[c_10,c_247])).

tff(c_1402,plain,(
    ! [B_230,B_231] :
      ( m1_subset_1('#skF_1'('#skF_4',B_230),B_231)
      | ~ r1_tarski('#skF_2',B_231)
      | B_230 = '#skF_4'
      | k1_relat_1(B_230) != '#skF_2'
      | ~ v1_funct_1(B_230)
      | ~ v1_relat_1(B_230) ) ),
    inference(resolution,[status(thm)],[c_1321,c_256])).

tff(c_48,plain,(
    ! [E_41] :
      ( k1_funct_1('#skF_5',E_41) = k1_funct_1('#skF_4',E_41)
      | ~ m1_subset_1(E_41,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1448,plain,(
    ! [B_230] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_230)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_230))
      | ~ r1_tarski('#skF_2','#skF_2')
      | B_230 = '#skF_4'
      | k1_relat_1(B_230) != '#skF_2'
      | ~ v1_funct_1(B_230)
      | ~ v1_relat_1(B_230) ) ),
    inference(resolution,[status(thm)],[c_1402,c_48])).

tff(c_1592,plain,(
    ! [B_243] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_243)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_243))
      | B_243 = '#skF_4'
      | k1_relat_1(B_243) != '#skF_2'
      | ~ v1_funct_1(B_243)
      | ~ v1_relat_1(B_243) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1152,c_1448])).

tff(c_18,plain,(
    ! [B_15,A_11] :
      ( k1_funct_1(B_15,'#skF_1'(A_11,B_15)) != k1_funct_1(A_11,'#skF_1'(A_11,B_15))
      | B_15 = A_11
      | k1_relat_1(B_15) != k1_relat_1(A_11)
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1599,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | '#skF_5' = '#skF_4'
    | k1_relat_1('#skF_5') != '#skF_2'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1592,c_18])).

tff(c_1606,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_54,c_1072,c_110,c_60,c_1088,c_1072,c_1599])).

tff(c_46,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1626,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1606,c_46])).

tff(c_1639,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1212,c_1626])).

tff(c_1640,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1060])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1657,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1640,c_2])).

tff(c_1659,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_246,c_1657])).

tff(c_1660,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1063])).

tff(c_1691,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1660,c_2])).

tff(c_1693,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_246,c_1691])).

tff(c_1694,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_242])).

tff(c_64,plain,(
    ! [B_43,A_44] :
      ( ~ v1_xboole_0(B_43)
      | B_43 = A_44
      | ~ v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_67,plain,(
    ! [A_44] :
      ( k1_xboole_0 = A_44
      | ~ v1_xboole_0(A_44) ) ),
    inference(resolution,[status(thm)],[c_2,c_64])).

tff(c_1701,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1694,c_67])).

tff(c_76,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | ~ m1_subset_1(A_49,k1_zfmisc_1(B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_92,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(resolution,[status(thm)],[c_6,c_76])).

tff(c_1722,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1701,c_92])).

tff(c_1725,plain,(
    ! [A_3] : m1_subset_1('#skF_4',k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1701,c_6])).

tff(c_1954,plain,(
    ! [A_290,B_291,C_292,D_293] :
      ( r2_relset_1(A_290,B_291,C_292,C_292)
      | ~ m1_subset_1(D_293,k1_zfmisc_1(k2_zfmisc_1(A_290,B_291)))
      | ~ m1_subset_1(C_292,k1_zfmisc_1(k2_zfmisc_1(A_290,B_291))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2166,plain,(
    ! [A_321,B_322,C_323,A_324] :
      ( r2_relset_1(A_321,B_322,C_323,C_323)
      | ~ m1_subset_1(C_323,k1_zfmisc_1(k2_zfmisc_1(A_321,B_322)))
      | ~ r1_tarski(A_324,k2_zfmisc_1(A_321,B_322)) ) ),
    inference(resolution,[status(thm)],[c_10,c_1954])).

tff(c_2175,plain,(
    ! [A_325,B_326,A_327] :
      ( r2_relset_1(A_325,B_326,'#skF_4','#skF_4')
      | ~ r1_tarski(A_327,k2_zfmisc_1(A_325,B_326)) ) ),
    inference(resolution,[status(thm)],[c_1725,c_2166])).

tff(c_2183,plain,(
    ! [A_325,B_326] : r2_relset_1(A_325,B_326,'#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_1722,c_2175])).

tff(c_1695,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_242])).

tff(c_243,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_226])).

tff(c_1711,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1695,c_243])).

tff(c_1717,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1711,c_67])).

tff(c_1749,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1701,c_1717])).

tff(c_1708,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1695,c_67])).

tff(c_1733,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1701,c_1708])).

tff(c_1741,plain,(
    ~ r2_relset_1('#skF_2','#skF_4','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1733,c_46])).

tff(c_1845,plain,(
    ~ r2_relset_1('#skF_2','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1749,c_1741])).

tff(c_2188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2183,c_1845])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:15:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.13/1.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.13/1.73  
% 4.13/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.13/1.74  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.13/1.74  
% 4.13/1.74  %Foreground sorts:
% 4.13/1.74  
% 4.13/1.74  
% 4.13/1.74  %Background operators:
% 4.13/1.74  
% 4.13/1.74  
% 4.13/1.74  %Foreground operators:
% 4.13/1.74  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.13/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.13/1.74  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.13/1.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.13/1.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.13/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.13/1.74  tff('#skF_5', type, '#skF_5': $i).
% 4.13/1.74  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.13/1.74  tff('#skF_2', type, '#skF_2': $i).
% 4.13/1.74  tff('#skF_3', type, '#skF_3': $i).
% 4.13/1.74  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.13/1.74  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.13/1.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.13/1.74  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.13/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.13/1.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.13/1.74  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.13/1.74  tff('#skF_4', type, '#skF_4': $i).
% 4.13/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.13/1.74  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.13/1.74  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.13/1.74  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.13/1.74  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.13/1.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.13/1.74  
% 4.41/1.75  tff(f_136, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_funct_2)).
% 4.41/1.75  tff(f_87, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 4.41/1.75  tff(f_36, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.41/1.75  tff(f_97, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 4.41/1.75  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.41/1.75  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.41/1.75  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.41/1.75  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.41/1.75  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 4.41/1.75  tff(f_70, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 4.41/1.75  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.41/1.75  tff(f_46, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 4.41/1.75  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.41/1.75  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 4.41/1.75  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.41/1.75  tff(c_226, plain, (![C_77, B_78, A_79]: (v1_xboole_0(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(B_78, A_79))) | ~v1_xboole_0(A_79))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.41/1.75  tff(c_242, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_56, c_226])).
% 4.41/1.75  tff(c_246, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_242])).
% 4.41/1.75  tff(c_6, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.41/1.75  tff(c_1184, plain, (![A_189, B_190, C_191, D_192]: (r2_relset_1(A_189, B_190, C_191, C_191) | ~m1_subset_1(D_192, k1_zfmisc_1(k2_zfmisc_1(A_189, B_190))) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_189, B_190))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.41/1.75  tff(c_1200, plain, (![A_195, B_196, C_197]: (r2_relset_1(A_195, B_196, C_197, C_197) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(A_195, B_196))))), inference(resolution, [status(thm)], [c_6, c_1184])).
% 4.41/1.75  tff(c_1212, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_56, c_1200])).
% 4.41/1.75  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.41/1.75  tff(c_94, plain, (![C_52, A_53, B_54]: (v1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.41/1.75  tff(c_111, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_94])).
% 4.41/1.75  tff(c_54, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.41/1.75  tff(c_52, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.41/1.75  tff(c_284, plain, (![A_93, B_94, C_95]: (k1_relset_1(A_93, B_94, C_95)=k1_relat_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.41/1.75  tff(c_301, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_284])).
% 4.41/1.75  tff(c_1042, plain, (![B_177, A_178, C_179]: (k1_xboole_0=B_177 | k1_relset_1(A_178, B_177, C_179)=A_178 | ~v1_funct_2(C_179, A_178, B_177) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_178, B_177))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.41/1.75  tff(c_1052, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_1042])).
% 4.41/1.75  tff(c_1063, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_301, c_1052])).
% 4.41/1.75  tff(c_1072, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(splitLeft, [status(thm)], [c_1063])).
% 4.41/1.75  tff(c_110, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_94])).
% 4.41/1.75  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.41/1.75  tff(c_58, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.41/1.75  tff(c_300, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_284])).
% 4.41/1.75  tff(c_1049, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_1042])).
% 4.41/1.75  tff(c_1060, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_300, c_1049])).
% 4.41/1.75  tff(c_1088, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_1060])).
% 4.41/1.75  tff(c_162, plain, (![C_67, A_68, B_69]: (v4_relat_1(C_67, A_68) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.41/1.75  tff(c_179, plain, (v4_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_50, c_162])).
% 4.41/1.75  tff(c_16, plain, (![B_10, A_9]: (r1_tarski(k1_relat_1(B_10), A_9) | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.41/1.75  tff(c_1080, plain, (![A_9]: (r1_tarski('#skF_2', A_9) | ~v4_relat_1('#skF_5', A_9) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1072, c_16])).
% 4.41/1.75  tff(c_1148, plain, (![A_186]: (r1_tarski('#skF_2', A_186) | ~v4_relat_1('#skF_5', A_186))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_1080])).
% 4.41/1.75  tff(c_1152, plain, (r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_179, c_1148])).
% 4.41/1.75  tff(c_1250, plain, (![A_205, B_206]: (r2_hidden('#skF_1'(A_205, B_206), k1_relat_1(A_205)) | B_206=A_205 | k1_relat_1(B_206)!=k1_relat_1(A_205) | ~v1_funct_1(B_206) | ~v1_relat_1(B_206) | ~v1_funct_1(A_205) | ~v1_relat_1(A_205))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.41/1.75  tff(c_1255, plain, (![B_206]: (r2_hidden('#skF_1'('#skF_4', B_206), '#skF_2') | B_206='#skF_4' | k1_relat_1(B_206)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_206) | ~v1_relat_1(B_206) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1088, c_1250])).
% 4.41/1.75  tff(c_1321, plain, (![B_215]: (r2_hidden('#skF_1'('#skF_4', B_215), '#skF_2') | B_215='#skF_4' | k1_relat_1(B_215)!='#skF_2' | ~v1_funct_1(B_215) | ~v1_relat_1(B_215))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_60, c_1088, c_1255])).
% 4.41/1.75  tff(c_10, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.41/1.75  tff(c_247, plain, (![A_80, C_81, B_82]: (m1_subset_1(A_80, C_81) | ~m1_subset_1(B_82, k1_zfmisc_1(C_81)) | ~r2_hidden(A_80, B_82))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.41/1.75  tff(c_256, plain, (![A_80, B_5, A_4]: (m1_subset_1(A_80, B_5) | ~r2_hidden(A_80, A_4) | ~r1_tarski(A_4, B_5))), inference(resolution, [status(thm)], [c_10, c_247])).
% 4.41/1.75  tff(c_1402, plain, (![B_230, B_231]: (m1_subset_1('#skF_1'('#skF_4', B_230), B_231) | ~r1_tarski('#skF_2', B_231) | B_230='#skF_4' | k1_relat_1(B_230)!='#skF_2' | ~v1_funct_1(B_230) | ~v1_relat_1(B_230))), inference(resolution, [status(thm)], [c_1321, c_256])).
% 4.41/1.75  tff(c_48, plain, (![E_41]: (k1_funct_1('#skF_5', E_41)=k1_funct_1('#skF_4', E_41) | ~m1_subset_1(E_41, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.41/1.75  tff(c_1448, plain, (![B_230]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_230))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_230)) | ~r1_tarski('#skF_2', '#skF_2') | B_230='#skF_4' | k1_relat_1(B_230)!='#skF_2' | ~v1_funct_1(B_230) | ~v1_relat_1(B_230))), inference(resolution, [status(thm)], [c_1402, c_48])).
% 4.41/1.75  tff(c_1592, plain, (![B_243]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_243))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_243)) | B_243='#skF_4' | k1_relat_1(B_243)!='#skF_2' | ~v1_funct_1(B_243) | ~v1_relat_1(B_243))), inference(demodulation, [status(thm), theory('equality')], [c_1152, c_1448])).
% 4.41/1.75  tff(c_18, plain, (![B_15, A_11]: (k1_funct_1(B_15, '#skF_1'(A_11, B_15))!=k1_funct_1(A_11, '#skF_1'(A_11, B_15)) | B_15=A_11 | k1_relat_1(B_15)!=k1_relat_1(A_11) | ~v1_funct_1(B_15) | ~v1_relat_1(B_15) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.41/1.75  tff(c_1599, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | '#skF_5'='#skF_4' | k1_relat_1('#skF_5')!='#skF_2' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1592, c_18])).
% 4.41/1.75  tff(c_1606, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_111, c_54, c_1072, c_110, c_60, c_1088, c_1072, c_1599])).
% 4.41/1.75  tff(c_46, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.41/1.75  tff(c_1626, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1606, c_46])).
% 4.41/1.75  tff(c_1639, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1212, c_1626])).
% 4.41/1.75  tff(c_1640, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1060])).
% 4.41/1.75  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.41/1.75  tff(c_1657, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1640, c_2])).
% 4.41/1.75  tff(c_1659, plain, $false, inference(negUnitSimplification, [status(thm)], [c_246, c_1657])).
% 4.41/1.75  tff(c_1660, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1063])).
% 4.41/1.75  tff(c_1691, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1660, c_2])).
% 4.41/1.75  tff(c_1693, plain, $false, inference(negUnitSimplification, [status(thm)], [c_246, c_1691])).
% 4.41/1.75  tff(c_1694, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_242])).
% 4.41/1.75  tff(c_64, plain, (![B_43, A_44]: (~v1_xboole_0(B_43) | B_43=A_44 | ~v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.41/1.75  tff(c_67, plain, (![A_44]: (k1_xboole_0=A_44 | ~v1_xboole_0(A_44))), inference(resolution, [status(thm)], [c_2, c_64])).
% 4.41/1.75  tff(c_1701, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1694, c_67])).
% 4.41/1.75  tff(c_76, plain, (![A_49, B_50]: (r1_tarski(A_49, B_50) | ~m1_subset_1(A_49, k1_zfmisc_1(B_50)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.41/1.75  tff(c_92, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(resolution, [status(thm)], [c_6, c_76])).
% 4.41/1.75  tff(c_1722, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_1701, c_92])).
% 4.41/1.75  tff(c_1725, plain, (![A_3]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_1701, c_6])).
% 4.41/1.75  tff(c_1954, plain, (![A_290, B_291, C_292, D_293]: (r2_relset_1(A_290, B_291, C_292, C_292) | ~m1_subset_1(D_293, k1_zfmisc_1(k2_zfmisc_1(A_290, B_291))) | ~m1_subset_1(C_292, k1_zfmisc_1(k2_zfmisc_1(A_290, B_291))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.41/1.75  tff(c_2166, plain, (![A_321, B_322, C_323, A_324]: (r2_relset_1(A_321, B_322, C_323, C_323) | ~m1_subset_1(C_323, k1_zfmisc_1(k2_zfmisc_1(A_321, B_322))) | ~r1_tarski(A_324, k2_zfmisc_1(A_321, B_322)))), inference(resolution, [status(thm)], [c_10, c_1954])).
% 4.41/1.75  tff(c_2175, plain, (![A_325, B_326, A_327]: (r2_relset_1(A_325, B_326, '#skF_4', '#skF_4') | ~r1_tarski(A_327, k2_zfmisc_1(A_325, B_326)))), inference(resolution, [status(thm)], [c_1725, c_2166])).
% 4.41/1.75  tff(c_2183, plain, (![A_325, B_326]: (r2_relset_1(A_325, B_326, '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_1722, c_2175])).
% 4.41/1.75  tff(c_1695, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_242])).
% 4.41/1.75  tff(c_243, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_226])).
% 4.41/1.75  tff(c_1711, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1695, c_243])).
% 4.41/1.75  tff(c_1717, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_1711, c_67])).
% 4.41/1.75  tff(c_1749, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1701, c_1717])).
% 4.41/1.75  tff(c_1708, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1695, c_67])).
% 4.41/1.75  tff(c_1733, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1701, c_1708])).
% 4.41/1.75  tff(c_1741, plain, (~r2_relset_1('#skF_2', '#skF_4', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1733, c_46])).
% 4.41/1.75  tff(c_1845, plain, (~r2_relset_1('#skF_2', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1749, c_1741])).
% 4.41/1.75  tff(c_2188, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2183, c_1845])).
% 4.41/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.41/1.75  
% 4.41/1.75  Inference rules
% 4.41/1.75  ----------------------
% 4.41/1.75  #Ref     : 3
% 4.41/1.75  #Sup     : 363
% 4.41/1.75  #Fact    : 0
% 4.41/1.75  #Define  : 0
% 4.41/1.75  #Split   : 12
% 4.41/1.75  #Chain   : 0
% 4.41/1.75  #Close   : 0
% 4.41/1.75  
% 4.41/1.75  Ordering : KBO
% 4.41/1.75  
% 4.41/1.75  Simplification rules
% 4.41/1.75  ----------------------
% 4.41/1.75  #Subsume      : 57
% 4.41/1.75  #Demod        : 503
% 4.41/1.75  #Tautology    : 154
% 4.41/1.75  #SimpNegUnit  : 11
% 4.41/1.75  #BackRed      : 111
% 4.41/1.75  
% 4.41/1.75  #Partial instantiations: 0
% 4.41/1.75  #Strategies tried      : 1
% 4.41/1.75  
% 4.41/1.75  Timing (in seconds)
% 4.41/1.75  ----------------------
% 4.41/1.76  Preprocessing        : 0.34
% 4.41/1.76  Parsing              : 0.18
% 4.41/1.76  CNF conversion       : 0.02
% 4.41/1.76  Main loop            : 0.64
% 4.41/1.76  Inferencing          : 0.22
% 4.41/1.76  Reduction            : 0.22
% 4.41/1.76  Demodulation         : 0.16
% 4.41/1.76  BG Simplification    : 0.03
% 4.41/1.76  Subsumption          : 0.11
% 4.41/1.76  Abstraction          : 0.03
% 4.41/1.76  MUC search           : 0.00
% 4.41/1.76  Cooper               : 0.00
% 4.41/1.76  Total                : 1.02
% 4.41/1.76  Index Insertion      : 0.00
% 4.49/1.76  Index Deletion       : 0.00
% 4.49/1.76  Index Matching       : 0.00
% 4.49/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
