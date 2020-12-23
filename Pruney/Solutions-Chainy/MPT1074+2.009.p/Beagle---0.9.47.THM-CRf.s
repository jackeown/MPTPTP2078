%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:07 EST 2020

% Result     : Theorem 6.19s
% Output     : CNFRefutation 6.60s
% Verified   : 
% Statistics : Number of formulae       :  166 (2089 expanded)
%              Number of leaves         :   36 ( 741 expanded)
%              Depth                    :   27
%              Number of atoms          :  344 (7352 expanded)
%              Number of equality atoms :   64 (1514 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_127,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ v1_xboole_0(B)
       => ! [C] :
            ( ~ v1_xboole_0(C)
           => ! [D] :
                ( ( v1_funct_1(D)
                  & v1_funct_2(D,B,C)
                  & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
               => ( ! [E] :
                      ( m1_subset_1(E,B)
                     => r2_hidden(k3_funct_2(B,C,D,E),A) )
                 => r1_tarski(k2_relset_1(B,C,D),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_funct_2)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_75,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( k1_relat_1(C) = A
          & ! [D] :
              ( r2_hidden(D,A)
             => r2_hidden(k1_funct_1(C,D),B) ) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_88,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_151,plain,(
    ! [A_67,B_68,C_69] :
      ( k2_relset_1(A_67,B_68,C_69) = k2_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_160,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_151])).

tff(c_50,plain,(
    ~ r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_161,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_50])).

tff(c_58,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_56,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_62,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_82,plain,(
    ! [C_52,A_53,B_54] :
      ( v1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_91,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_82])).

tff(c_137,plain,(
    ! [A_64,B_65,C_66] :
      ( k1_relset_1(A_64,B_65,C_66) = k1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_146,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_137])).

tff(c_575,plain,(
    ! [B_122,A_123,C_124] :
      ( k1_xboole_0 = B_122
      | k1_relset_1(A_123,B_122,C_124) = A_123
      | ~ v1_funct_2(C_124,A_123,B_122)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_123,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_590,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_575])).

tff(c_597,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_146,c_590])).

tff(c_598,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_597])).

tff(c_44,plain,(
    ! [C_29,B_28] :
      ( r2_hidden('#skF_1'(k1_relat_1(C_29),B_28,C_29),k1_relat_1(C_29))
      | v1_funct_2(C_29,k1_relat_1(C_29),B_28)
      | ~ v1_funct_1(C_29)
      | ~ v1_relat_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_606,plain,(
    ! [B_28] :
      ( r2_hidden('#skF_1'(k1_relat_1('#skF_5'),B_28,'#skF_5'),'#skF_3')
      | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),B_28)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_598,c_44])).

tff(c_628,plain,(
    ! [B_127] :
      ( r2_hidden('#skF_1'('#skF_3',B_127,'#skF_5'),'#skF_3')
      | v1_funct_2('#skF_5','#skF_3',B_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_58,c_598,c_598,c_606])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,B_5)
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_632,plain,(
    ! [B_127] :
      ( m1_subset_1('#skF_1'('#skF_3',B_127,'#skF_5'),'#skF_3')
      | v1_funct_2('#skF_5','#skF_3',B_127) ) ),
    inference(resolution,[status(thm)],[c_628,c_10])).

tff(c_992,plain,(
    ! [A_161,B_162,C_163,D_164] :
      ( k3_funct_2(A_161,B_162,C_163,D_164) = k1_funct_1(C_163,D_164)
      | ~ m1_subset_1(D_164,A_161)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162)))
      | ~ v1_funct_2(C_163,A_161,B_162)
      | ~ v1_funct_1(C_163)
      | v1_xboole_0(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1002,plain,(
    ! [B_162,C_163,B_127] :
      ( k3_funct_2('#skF_3',B_162,C_163,'#skF_1'('#skF_3',B_127,'#skF_5')) = k1_funct_1(C_163,'#skF_1'('#skF_3',B_127,'#skF_5'))
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_162)))
      | ~ v1_funct_2(C_163,'#skF_3',B_162)
      | ~ v1_funct_1(C_163)
      | v1_xboole_0('#skF_3')
      | v1_funct_2('#skF_5','#skF_3',B_127) ) ),
    inference(resolution,[status(thm)],[c_632,c_992])).

tff(c_1229,plain,(
    ! [B_184,C_185,B_186] :
      ( k3_funct_2('#skF_3',B_184,C_185,'#skF_1'('#skF_3',B_186,'#skF_5')) = k1_funct_1(C_185,'#skF_1'('#skF_3',B_186,'#skF_5'))
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_184)))
      | ~ v1_funct_2(C_185,'#skF_3',B_184)
      | ~ v1_funct_1(C_185)
      | v1_funct_2('#skF_5','#skF_3',B_186) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1002])).

tff(c_1245,plain,(
    ! [B_186] :
      ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3',B_186,'#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3',B_186,'#skF_5'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5')
      | v1_funct_2('#skF_5','#skF_3',B_186) ) ),
    inference(resolution,[status(thm)],[c_54,c_1229])).

tff(c_2076,plain,(
    ! [B_271] :
      ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3',B_271,'#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3',B_271,'#skF_5'))
      | v1_funct_2('#skF_5','#skF_3',B_271) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1245])).

tff(c_52,plain,(
    ! [E_42] :
      ( r2_hidden(k3_funct_2('#skF_3','#skF_4','#skF_5',E_42),'#skF_2')
      | ~ m1_subset_1(E_42,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_2179,plain,(
    ! [B_278] :
      ( r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_278,'#skF_5')),'#skF_2')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_278,'#skF_5'),'#skF_3')
      | v1_funct_2('#skF_5','#skF_3',B_278) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2076,c_52])).

tff(c_633,plain,(
    ! [C_128,B_129] :
      ( ~ r2_hidden(k1_funct_1(C_128,'#skF_1'(k1_relat_1(C_128),B_129,C_128)),B_129)
      | v1_funct_2(C_128,k1_relat_1(C_128),B_129)
      | ~ v1_funct_1(C_128)
      | ~ v1_relat_1(C_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_636,plain,(
    ! [B_129] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_129,'#skF_5')),B_129)
      | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),B_129)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_598,c_633])).

tff(c_638,plain,(
    ! [B_129] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_129,'#skF_5')),B_129)
      | v1_funct_2('#skF_5','#skF_3',B_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_58,c_598,c_636])).

tff(c_2192,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3')
    | v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_2179,c_638])).

tff(c_2194,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2192])).

tff(c_739,plain,(
    ! [C_142,B_143] :
      ( r2_hidden('#skF_1'(k1_relat_1(C_142),B_143,C_142),k1_relat_1(C_142))
      | m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_142),B_143)))
      | ~ v1_funct_1(C_142)
      | ~ v1_relat_1(C_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_745,plain,(
    ! [B_143] :
      ( r2_hidden('#skF_1'('#skF_3',B_143,'#skF_5'),k1_relat_1('#skF_5'))
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),B_143)))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_598,c_739])).

tff(c_754,plain,(
    ! [B_144] :
      ( r2_hidden('#skF_1'('#skF_3',B_144,'#skF_5'),'#skF_3')
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_144))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_58,c_598,c_598,c_745])).

tff(c_22,plain,(
    ! [A_17,B_18,C_19] :
      ( k2_relset_1(A_17,B_18,C_19) = k2_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_871,plain,(
    ! [B_152] :
      ( k2_relset_1('#skF_3',B_152,'#skF_5') = k2_relat_1('#skF_5')
      | r2_hidden('#skF_1'('#skF_3',B_152,'#skF_5'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_754,c_22])).

tff(c_875,plain,(
    ! [B_152] :
      ( m1_subset_1('#skF_1'('#skF_3',B_152,'#skF_5'),'#skF_3')
      | k2_relset_1('#skF_3',B_152,'#skF_5') = k2_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_871,c_10])).

tff(c_2240,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_875,c_2194])).

tff(c_229,plain,(
    ! [A_84,B_85,C_86] :
      ( m1_subset_1(k2_relset_1(A_84,B_85,C_86),k1_zfmisc_1(B_85))
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_254,plain,(
    ! [A_84,B_85,C_86] :
      ( r1_tarski(k2_relset_1(A_84,B_85,C_86),B_85)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(resolution,[status(thm)],[c_229,c_12])).

tff(c_835,plain,(
    ! [B_151] :
      ( r1_tarski(k2_relset_1('#skF_3',B_151,'#skF_5'),B_151)
      | r2_hidden('#skF_1'('#skF_3',B_151,'#skF_5'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_754,c_254])).

tff(c_870,plain,(
    ! [B_151] :
      ( m1_subset_1('#skF_1'('#skF_3',B_151,'#skF_5'),'#skF_3')
      | r1_tarski(k2_relset_1('#skF_3',B_151,'#skF_5'),B_151) ) ),
    inference(resolution,[status(thm)],[c_835,c_10])).

tff(c_2257,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3')
    | r1_tarski(k2_relat_1('#skF_5'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2240,c_870])).

tff(c_2272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_161,c_2194,c_2257])).

tff(c_2274,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_2192])).

tff(c_36,plain,(
    ! [A_23,B_24,C_25,D_26] :
      ( k3_funct_2(A_23,B_24,C_25,D_26) = k1_funct_1(C_25,D_26)
      | ~ m1_subset_1(D_26,A_23)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24)))
      | ~ v1_funct_2(C_25,A_23,B_24)
      | ~ v1_funct_1(C_25)
      | v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2308,plain,(
    ! [B_24,C_25] :
      ( k3_funct_2('#skF_3',B_24,C_25,'#skF_1'('#skF_3','#skF_2','#skF_5')) = k1_funct_1(C_25,'#skF_1'('#skF_3','#skF_2','#skF_5'))
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_24)))
      | ~ v1_funct_2(C_25,'#skF_3',B_24)
      | ~ v1_funct_1(C_25)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2274,c_36])).

tff(c_2402,plain,(
    ! [B_289,C_290] :
      ( k3_funct_2('#skF_3',B_289,C_290,'#skF_1'('#skF_3','#skF_2','#skF_5')) = k1_funct_1(C_290,'#skF_1'('#skF_3','#skF_2','#skF_5'))
      | ~ m1_subset_1(C_290,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_289)))
      | ~ v1_funct_2(C_290,'#skF_3',B_289)
      | ~ v1_funct_1(C_290) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2308])).

tff(c_2431,plain,
    ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5'))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_2402])).

tff(c_2445,plain,(
    k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_2431])).

tff(c_2455,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')),'#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2445,c_52])).

tff(c_2466,plain,(
    r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2274,c_2455])).

tff(c_829,plain,(
    ! [C_149,B_150] :
      ( ~ r2_hidden(k1_funct_1(C_149,'#skF_1'(k1_relat_1(C_149),B_150,C_149)),B_150)
      | m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_149),B_150)))
      | ~ v1_funct_1(C_149)
      | ~ v1_relat_1(C_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_832,plain,(
    ! [B_150] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_150,'#skF_5')),B_150)
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),B_150)))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_598,c_829])).

tff(c_834,plain,(
    ! [B_150] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_150,'#skF_5')),B_150)
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_150))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_58,c_598,c_832])).

tff(c_2482,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_2466,c_834])).

tff(c_2553,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2482,c_12])).

tff(c_2548,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2482,c_22])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_453,plain,(
    ! [A_105,B_106,C_107] :
      ( r1_tarski(k2_relset_1(A_105,B_106,C_107),B_106)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(resolution,[status(thm)],[c_229,c_12])).

tff(c_468,plain,(
    ! [A_105,B_106,A_6] :
      ( r1_tarski(k2_relset_1(A_105,B_106,A_6),B_106)
      | ~ r1_tarski(A_6,k2_zfmisc_1(A_105,B_106)) ) ),
    inference(resolution,[status(thm)],[c_14,c_453])).

tff(c_2617,plain,
    ( r1_tarski(k2_relat_1('#skF_5'),'#skF_2')
    | ~ r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2548,c_468])).

tff(c_2630,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2553,c_2617])).

tff(c_2632,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_161,c_2630])).

tff(c_2633,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_597])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2651,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2633,c_8])).

tff(c_250,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_229])).

tff(c_256,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_250])).

tff(c_260,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_256,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_263,plain,
    ( k2_relat_1('#skF_5') = '#skF_4'
    | ~ r1_tarski('#skF_4',k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_260,c_2])).

tff(c_264,plain,(
    ~ r1_tarski('#skF_4',k2_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_263])).

tff(c_2658,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2651,c_264])).

tff(c_2659,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_263])).

tff(c_2663,plain,(
    ~ r1_tarski('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2659,c_161])).

tff(c_2858,plain,(
    ! [B_309,A_310,C_311] :
      ( k1_xboole_0 = B_309
      | k1_relset_1(A_310,B_309,C_311) = A_310
      | ~ v1_funct_2(C_311,A_310,B_309)
      | ~ m1_subset_1(C_311,k1_zfmisc_1(k2_zfmisc_1(A_310,B_309))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2873,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_2858])).

tff(c_2880,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_146,c_2873])).

tff(c_2881,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2880])).

tff(c_2893,plain,(
    ! [C_312,B_313] :
      ( r2_hidden('#skF_1'(k1_relat_1(C_312),B_313,C_312),k1_relat_1(C_312))
      | v1_funct_2(C_312,k1_relat_1(C_312),B_313)
      | ~ v1_funct_1(C_312)
      | ~ v1_relat_1(C_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2899,plain,(
    ! [B_313] :
      ( r2_hidden('#skF_1'('#skF_3',B_313,'#skF_5'),k1_relat_1('#skF_5'))
      | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),B_313)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2881,c_2893])).

tff(c_2917,plain,(
    ! [B_315] :
      ( r2_hidden('#skF_1'('#skF_3',B_315,'#skF_5'),'#skF_3')
      | v1_funct_2('#skF_5','#skF_3',B_315) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_58,c_2881,c_2881,c_2899])).

tff(c_2921,plain,(
    ! [B_315] :
      ( m1_subset_1('#skF_1'('#skF_3',B_315,'#skF_5'),'#skF_3')
      | v1_funct_2('#skF_5','#skF_3',B_315) ) ),
    inference(resolution,[status(thm)],[c_2917,c_10])).

tff(c_3274,plain,(
    ! [A_358,B_359,C_360,D_361] :
      ( k3_funct_2(A_358,B_359,C_360,D_361) = k1_funct_1(C_360,D_361)
      | ~ m1_subset_1(D_361,A_358)
      | ~ m1_subset_1(C_360,k1_zfmisc_1(k2_zfmisc_1(A_358,B_359)))
      | ~ v1_funct_2(C_360,A_358,B_359)
      | ~ v1_funct_1(C_360)
      | v1_xboole_0(A_358) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_3284,plain,(
    ! [B_359,C_360,B_315] :
      ( k3_funct_2('#skF_3',B_359,C_360,'#skF_1'('#skF_3',B_315,'#skF_5')) = k1_funct_1(C_360,'#skF_1'('#skF_3',B_315,'#skF_5'))
      | ~ m1_subset_1(C_360,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_359)))
      | ~ v1_funct_2(C_360,'#skF_3',B_359)
      | ~ v1_funct_1(C_360)
      | v1_xboole_0('#skF_3')
      | v1_funct_2('#skF_5','#skF_3',B_315) ) ),
    inference(resolution,[status(thm)],[c_2921,c_3274])).

tff(c_3559,plain,(
    ! [B_383,C_384,B_385] :
      ( k3_funct_2('#skF_3',B_383,C_384,'#skF_1'('#skF_3',B_385,'#skF_5')) = k1_funct_1(C_384,'#skF_1'('#skF_3',B_385,'#skF_5'))
      | ~ m1_subset_1(C_384,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_383)))
      | ~ v1_funct_2(C_384,'#skF_3',B_383)
      | ~ v1_funct_1(C_384)
      | v1_funct_2('#skF_5','#skF_3',B_385) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_3284])).

tff(c_3572,plain,(
    ! [B_385] :
      ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3',B_385,'#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3',B_385,'#skF_5'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5')
      | v1_funct_2('#skF_5','#skF_3',B_385) ) ),
    inference(resolution,[status(thm)],[c_54,c_3559])).

tff(c_4473,plain,(
    ! [B_467] :
      ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3',B_467,'#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3',B_467,'#skF_5'))
      | v1_funct_2('#skF_5','#skF_3',B_467) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_3572])).

tff(c_4559,plain,(
    ! [B_480] :
      ( r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_480,'#skF_5')),'#skF_2')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_480,'#skF_5'),'#skF_3')
      | v1_funct_2('#skF_5','#skF_3',B_480) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4473,c_52])).

tff(c_2967,plain,(
    ! [C_324,B_325] :
      ( ~ r2_hidden(k1_funct_1(C_324,'#skF_1'(k1_relat_1(C_324),B_325,C_324)),B_325)
      | v1_funct_2(C_324,k1_relat_1(C_324),B_325)
      | ~ v1_funct_1(C_324)
      | ~ v1_relat_1(C_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2970,plain,(
    ! [B_325] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_325,'#skF_5')),B_325)
      | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),B_325)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2881,c_2967])).

tff(c_2972,plain,(
    ! [B_325] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_325,'#skF_5')),B_325)
      | v1_funct_2('#skF_5','#skF_3',B_325) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_58,c_2881,c_2970])).

tff(c_4572,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3')
    | v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_4559,c_2972])).

tff(c_4574,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_4572])).

tff(c_3067,plain,(
    ! [C_335,B_336] :
      ( r2_hidden('#skF_1'(k1_relat_1(C_335),B_336,C_335),k1_relat_1(C_335))
      | m1_subset_1(C_335,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_335),B_336)))
      | ~ v1_funct_1(C_335)
      | ~ v1_relat_1(C_335) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_3073,plain,(
    ! [B_336] :
      ( r2_hidden('#skF_1'('#skF_3',B_336,'#skF_5'),k1_relat_1('#skF_5'))
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),B_336)))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2881,c_3067])).

tff(c_3159,plain,(
    ! [B_348] :
      ( r2_hidden('#skF_1'('#skF_3',B_348,'#skF_5'),'#skF_3')
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_348))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_58,c_2881,c_2881,c_3073])).

tff(c_3174,plain,(
    ! [B_348] :
      ( k2_relset_1('#skF_3',B_348,'#skF_5') = k2_relat_1('#skF_5')
      | r2_hidden('#skF_1'('#skF_3',B_348,'#skF_5'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_3159,c_22])).

tff(c_3211,plain,(
    ! [B_353] :
      ( k2_relset_1('#skF_3',B_353,'#skF_5') = '#skF_4'
      | r2_hidden('#skF_1'('#skF_3',B_353,'#skF_5'),'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2659,c_3174])).

tff(c_3215,plain,(
    ! [B_353] :
      ( m1_subset_1('#skF_1'('#skF_3',B_353,'#skF_5'),'#skF_3')
      | k2_relset_1('#skF_3',B_353,'#skF_5') = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_3211,c_10])).

tff(c_4584,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3215,c_4574])).

tff(c_3243,plain,(
    ! [B_357] :
      ( r1_tarski(k2_relset_1('#skF_3',B_357,'#skF_5'),B_357)
      | r2_hidden('#skF_1'('#skF_3',B_357,'#skF_5'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_3159,c_254])).

tff(c_3273,plain,(
    ! [B_357] :
      ( m1_subset_1('#skF_1'('#skF_3',B_357,'#skF_5'),'#skF_3')
      | r1_tarski(k2_relset_1('#skF_3',B_357,'#skF_5'),B_357) ) ),
    inference(resolution,[status(thm)],[c_3243,c_10])).

tff(c_4597,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3')
    | r1_tarski('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4584,c_3273])).

tff(c_4612,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2663,c_4574,c_4597])).

tff(c_4614,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_4572])).

tff(c_4631,plain,(
    ! [B_24,C_25] :
      ( k3_funct_2('#skF_3',B_24,C_25,'#skF_1'('#skF_3','#skF_2','#skF_5')) = k1_funct_1(C_25,'#skF_1'('#skF_3','#skF_2','#skF_5'))
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_24)))
      | ~ v1_funct_2(C_25,'#skF_3',B_24)
      | ~ v1_funct_1(C_25)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_4614,c_36])).

tff(c_4671,plain,(
    ! [B_485,C_486] :
      ( k3_funct_2('#skF_3',B_485,C_486,'#skF_1'('#skF_3','#skF_2','#skF_5')) = k1_funct_1(C_486,'#skF_1'('#skF_3','#skF_2','#skF_5'))
      | ~ m1_subset_1(C_486,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_485)))
      | ~ v1_funct_2(C_486,'#skF_3',B_485)
      | ~ v1_funct_1(C_486) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_4631])).

tff(c_4700,plain,
    ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5'))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_4671])).

tff(c_4714,plain,(
    k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_4700])).

tff(c_4724,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')),'#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4714,c_52])).

tff(c_4735,plain,(
    r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4614,c_4724])).

tff(c_3205,plain,(
    ! [C_351,B_352] :
      ( ~ r2_hidden(k1_funct_1(C_351,'#skF_1'(k1_relat_1(C_351),B_352,C_351)),B_352)
      | m1_subset_1(C_351,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_351),B_352)))
      | ~ v1_funct_1(C_351)
      | ~ v1_relat_1(C_351) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_3208,plain,(
    ! [B_352] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_352,'#skF_5')),B_352)
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),B_352)))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2881,c_3205])).

tff(c_3210,plain,(
    ! [B_352] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_352,'#skF_5')),B_352)
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_352))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_58,c_2881,c_3208])).

tff(c_4751,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_4735,c_3210])).

tff(c_4782,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_4751,c_22])).

tff(c_4818,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2659,c_4782])).

tff(c_18,plain,(
    ! [A_11,B_12,C_13] :
      ( m1_subset_1(k2_relset_1(A_11,B_12,C_13),k1_zfmisc_1(B_12))
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4841,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4818,c_18])).

tff(c_4851,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4751,c_4841])).

tff(c_4873,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_4851,c_12])).

tff(c_4878,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2663,c_4873])).

tff(c_4879,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2880])).

tff(c_4892,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4879,c_8])).

tff(c_4899,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4892,c_2663])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:23:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.19/2.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.19/2.36  
% 6.19/2.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.19/2.36  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 6.19/2.36  
% 6.19/2.36  %Foreground sorts:
% 6.19/2.36  
% 6.19/2.36  
% 6.19/2.36  %Background operators:
% 6.19/2.36  
% 6.19/2.36  
% 6.19/2.36  %Foreground operators:
% 6.19/2.36  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.19/2.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.19/2.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.19/2.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.19/2.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.19/2.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.19/2.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.19/2.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.19/2.36  tff('#skF_5', type, '#skF_5': $i).
% 6.19/2.36  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.19/2.36  tff('#skF_2', type, '#skF_2': $i).
% 6.19/2.36  tff('#skF_3', type, '#skF_3': $i).
% 6.19/2.36  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.19/2.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.19/2.36  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.19/2.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.19/2.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.19/2.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.19/2.36  tff('#skF_4', type, '#skF_4': $i).
% 6.19/2.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.19/2.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.19/2.36  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 6.19/2.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.19/2.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.19/2.36  
% 6.60/2.40  tff(f_127, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((![E]: (m1_subset_1(E, B) => r2_hidden(k3_funct_2(B, C, D, E), A))) => r1_tarski(k2_relset_1(B, C, D), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t191_funct_2)).
% 6.60/2.40  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.60/2.40  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.60/2.40  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.60/2.40  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.60/2.40  tff(f_105, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_funct_2)).
% 6.60/2.40  tff(f_37, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 6.60/2.40  tff(f_88, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 6.60/2.40  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 6.60/2.40  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.60/2.40  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.60/2.40  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.60/2.40  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.60/2.40  tff(c_151, plain, (![A_67, B_68, C_69]: (k2_relset_1(A_67, B_68, C_69)=k2_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.60/2.40  tff(c_160, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_151])).
% 6.60/2.40  tff(c_50, plain, (~r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.60/2.40  tff(c_161, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_50])).
% 6.60/2.40  tff(c_58, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.60/2.40  tff(c_56, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.60/2.40  tff(c_62, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.60/2.40  tff(c_82, plain, (![C_52, A_53, B_54]: (v1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.60/2.40  tff(c_91, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_82])).
% 6.60/2.40  tff(c_137, plain, (![A_64, B_65, C_66]: (k1_relset_1(A_64, B_65, C_66)=k1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.60/2.40  tff(c_146, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_137])).
% 6.60/2.40  tff(c_575, plain, (![B_122, A_123, C_124]: (k1_xboole_0=B_122 | k1_relset_1(A_123, B_122, C_124)=A_123 | ~v1_funct_2(C_124, A_123, B_122) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_123, B_122))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.60/2.40  tff(c_590, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_54, c_575])).
% 6.60/2.40  tff(c_597, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_146, c_590])).
% 6.60/2.40  tff(c_598, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_597])).
% 6.60/2.40  tff(c_44, plain, (![C_29, B_28]: (r2_hidden('#skF_1'(k1_relat_1(C_29), B_28, C_29), k1_relat_1(C_29)) | v1_funct_2(C_29, k1_relat_1(C_29), B_28) | ~v1_funct_1(C_29) | ~v1_relat_1(C_29))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.60/2.40  tff(c_606, plain, (![B_28]: (r2_hidden('#skF_1'(k1_relat_1('#skF_5'), B_28, '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), B_28) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_598, c_44])).
% 6.60/2.40  tff(c_628, plain, (![B_127]: (r2_hidden('#skF_1'('#skF_3', B_127, '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', '#skF_3', B_127))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_58, c_598, c_598, c_606])).
% 6.60/2.40  tff(c_10, plain, (![A_4, B_5]: (m1_subset_1(A_4, B_5) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.60/2.40  tff(c_632, plain, (![B_127]: (m1_subset_1('#skF_1'('#skF_3', B_127, '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', '#skF_3', B_127))), inference(resolution, [status(thm)], [c_628, c_10])).
% 6.60/2.40  tff(c_992, plain, (![A_161, B_162, C_163, D_164]: (k3_funct_2(A_161, B_162, C_163, D_164)=k1_funct_1(C_163, D_164) | ~m1_subset_1(D_164, A_161) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))) | ~v1_funct_2(C_163, A_161, B_162) | ~v1_funct_1(C_163) | v1_xboole_0(A_161))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.60/2.40  tff(c_1002, plain, (![B_162, C_163, B_127]: (k3_funct_2('#skF_3', B_162, C_163, '#skF_1'('#skF_3', B_127, '#skF_5'))=k1_funct_1(C_163, '#skF_1'('#skF_3', B_127, '#skF_5')) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_162))) | ~v1_funct_2(C_163, '#skF_3', B_162) | ~v1_funct_1(C_163) | v1_xboole_0('#skF_3') | v1_funct_2('#skF_5', '#skF_3', B_127))), inference(resolution, [status(thm)], [c_632, c_992])).
% 6.60/2.40  tff(c_1229, plain, (![B_184, C_185, B_186]: (k3_funct_2('#skF_3', B_184, C_185, '#skF_1'('#skF_3', B_186, '#skF_5'))=k1_funct_1(C_185, '#skF_1'('#skF_3', B_186, '#skF_5')) | ~m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_184))) | ~v1_funct_2(C_185, '#skF_3', B_184) | ~v1_funct_1(C_185) | v1_funct_2('#skF_5', '#skF_3', B_186))), inference(negUnitSimplification, [status(thm)], [c_62, c_1002])).
% 6.60/2.40  tff(c_1245, plain, (![B_186]: (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', B_186, '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_186, '#skF_5')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_funct_2('#skF_5', '#skF_3', B_186))), inference(resolution, [status(thm)], [c_54, c_1229])).
% 6.60/2.40  tff(c_2076, plain, (![B_271]: (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', B_271, '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_271, '#skF_5')) | v1_funct_2('#skF_5', '#skF_3', B_271))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_1245])).
% 6.60/2.40  tff(c_52, plain, (![E_42]: (r2_hidden(k3_funct_2('#skF_3', '#skF_4', '#skF_5', E_42), '#skF_2') | ~m1_subset_1(E_42, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.60/2.40  tff(c_2179, plain, (![B_278]: (r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_278, '#skF_5')), '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', B_278, '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', '#skF_3', B_278))), inference(superposition, [status(thm), theory('equality')], [c_2076, c_52])).
% 6.60/2.40  tff(c_633, plain, (![C_128, B_129]: (~r2_hidden(k1_funct_1(C_128, '#skF_1'(k1_relat_1(C_128), B_129, C_128)), B_129) | v1_funct_2(C_128, k1_relat_1(C_128), B_129) | ~v1_funct_1(C_128) | ~v1_relat_1(C_128))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.60/2.40  tff(c_636, plain, (![B_129]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_129, '#skF_5')), B_129) | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), B_129) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_598, c_633])).
% 6.60/2.40  tff(c_638, plain, (![B_129]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_129, '#skF_5')), B_129) | v1_funct_2('#skF_5', '#skF_3', B_129))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_58, c_598, c_636])).
% 6.60/2.40  tff(c_2192, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_2179, c_638])).
% 6.60/2.40  tff(c_2194, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_2192])).
% 6.60/2.40  tff(c_739, plain, (![C_142, B_143]: (r2_hidden('#skF_1'(k1_relat_1(C_142), B_143, C_142), k1_relat_1(C_142)) | m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_142), B_143))) | ~v1_funct_1(C_142) | ~v1_relat_1(C_142))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.60/2.40  tff(c_745, plain, (![B_143]: (r2_hidden('#skF_1'('#skF_3', B_143, '#skF_5'), k1_relat_1('#skF_5')) | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), B_143))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_598, c_739])).
% 6.60/2.40  tff(c_754, plain, (![B_144]: (r2_hidden('#skF_1'('#skF_3', B_144, '#skF_5'), '#skF_3') | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_144))))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_58, c_598, c_598, c_745])).
% 6.60/2.40  tff(c_22, plain, (![A_17, B_18, C_19]: (k2_relset_1(A_17, B_18, C_19)=k2_relat_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.60/2.40  tff(c_871, plain, (![B_152]: (k2_relset_1('#skF_3', B_152, '#skF_5')=k2_relat_1('#skF_5') | r2_hidden('#skF_1'('#skF_3', B_152, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_754, c_22])).
% 6.60/2.40  tff(c_875, plain, (![B_152]: (m1_subset_1('#skF_1'('#skF_3', B_152, '#skF_5'), '#skF_3') | k2_relset_1('#skF_3', B_152, '#skF_5')=k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_871, c_10])).
% 6.60/2.40  tff(c_2240, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_875, c_2194])).
% 6.60/2.40  tff(c_229, plain, (![A_84, B_85, C_86]: (m1_subset_1(k2_relset_1(A_84, B_85, C_86), k1_zfmisc_1(B_85)) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.60/2.40  tff(c_12, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.60/2.40  tff(c_254, plain, (![A_84, B_85, C_86]: (r1_tarski(k2_relset_1(A_84, B_85, C_86), B_85) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(resolution, [status(thm)], [c_229, c_12])).
% 6.60/2.40  tff(c_835, plain, (![B_151]: (r1_tarski(k2_relset_1('#skF_3', B_151, '#skF_5'), B_151) | r2_hidden('#skF_1'('#skF_3', B_151, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_754, c_254])).
% 6.60/2.40  tff(c_870, plain, (![B_151]: (m1_subset_1('#skF_1'('#skF_3', B_151, '#skF_5'), '#skF_3') | r1_tarski(k2_relset_1('#skF_3', B_151, '#skF_5'), B_151))), inference(resolution, [status(thm)], [c_835, c_10])).
% 6.60/2.40  tff(c_2257, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3') | r1_tarski(k2_relat_1('#skF_5'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2240, c_870])).
% 6.60/2.40  tff(c_2272, plain, $false, inference(negUnitSimplification, [status(thm)], [c_161, c_2194, c_2257])).
% 6.60/2.40  tff(c_2274, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(splitRight, [status(thm)], [c_2192])).
% 6.60/2.40  tff(c_36, plain, (![A_23, B_24, C_25, D_26]: (k3_funct_2(A_23, B_24, C_25, D_26)=k1_funct_1(C_25, D_26) | ~m1_subset_1(D_26, A_23) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))) | ~v1_funct_2(C_25, A_23, B_24) | ~v1_funct_1(C_25) | v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.60/2.40  tff(c_2308, plain, (![B_24, C_25]: (k3_funct_2('#skF_3', B_24, C_25, '#skF_1'('#skF_3', '#skF_2', '#skF_5'))=k1_funct_1(C_25, '#skF_1'('#skF_3', '#skF_2', '#skF_5')) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_24))) | ~v1_funct_2(C_25, '#skF_3', B_24) | ~v1_funct_1(C_25) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_2274, c_36])).
% 6.60/2.40  tff(c_2402, plain, (![B_289, C_290]: (k3_funct_2('#skF_3', B_289, C_290, '#skF_1'('#skF_3', '#skF_2', '#skF_5'))=k1_funct_1(C_290, '#skF_1'('#skF_3', '#skF_2', '#skF_5')) | ~m1_subset_1(C_290, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_289))) | ~v1_funct_2(C_290, '#skF_3', B_289) | ~v1_funct_1(C_290))), inference(negUnitSimplification, [status(thm)], [c_62, c_2308])).
% 6.60/2.40  tff(c_2431, plain, (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_2402])).
% 6.60/2.40  tff(c_2445, plain, (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_2431])).
% 6.60/2.40  tff(c_2455, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5')), '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2445, c_52])).
% 6.60/2.40  tff(c_2466, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2274, c_2455])).
% 6.60/2.40  tff(c_829, plain, (![C_149, B_150]: (~r2_hidden(k1_funct_1(C_149, '#skF_1'(k1_relat_1(C_149), B_150, C_149)), B_150) | m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_149), B_150))) | ~v1_funct_1(C_149) | ~v1_relat_1(C_149))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.60/2.40  tff(c_832, plain, (![B_150]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_150, '#skF_5')), B_150) | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), B_150))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_598, c_829])).
% 6.60/2.40  tff(c_834, plain, (![B_150]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_150, '#skF_5')), B_150) | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_150))))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_58, c_598, c_832])).
% 6.60/2.40  tff(c_2482, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_2466, c_834])).
% 6.60/2.40  tff(c_2553, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_2482, c_12])).
% 6.60/2.40  tff(c_2548, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2482, c_22])).
% 6.60/2.40  tff(c_14, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.60/2.40  tff(c_453, plain, (![A_105, B_106, C_107]: (r1_tarski(k2_relset_1(A_105, B_106, C_107), B_106) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(resolution, [status(thm)], [c_229, c_12])).
% 6.60/2.40  tff(c_468, plain, (![A_105, B_106, A_6]: (r1_tarski(k2_relset_1(A_105, B_106, A_6), B_106) | ~r1_tarski(A_6, k2_zfmisc_1(A_105, B_106)))), inference(resolution, [status(thm)], [c_14, c_453])).
% 6.60/2.40  tff(c_2617, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_2') | ~r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2548, c_468])).
% 6.60/2.40  tff(c_2630, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2553, c_2617])).
% 6.60/2.40  tff(c_2632, plain, $false, inference(negUnitSimplification, [status(thm)], [c_161, c_2630])).
% 6.60/2.40  tff(c_2633, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_597])).
% 6.60/2.40  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.60/2.40  tff(c_2651, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2633, c_8])).
% 6.60/2.40  tff(c_250, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_160, c_229])).
% 6.60/2.40  tff(c_256, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_250])).
% 6.60/2.40  tff(c_260, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_256, c_12])).
% 6.60/2.40  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.60/2.40  tff(c_263, plain, (k2_relat_1('#skF_5')='#skF_4' | ~r1_tarski('#skF_4', k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_260, c_2])).
% 6.60/2.40  tff(c_264, plain, (~r1_tarski('#skF_4', k2_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_263])).
% 6.60/2.40  tff(c_2658, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2651, c_264])).
% 6.60/2.40  tff(c_2659, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_263])).
% 6.60/2.40  tff(c_2663, plain, (~r1_tarski('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2659, c_161])).
% 6.60/2.40  tff(c_2858, plain, (![B_309, A_310, C_311]: (k1_xboole_0=B_309 | k1_relset_1(A_310, B_309, C_311)=A_310 | ~v1_funct_2(C_311, A_310, B_309) | ~m1_subset_1(C_311, k1_zfmisc_1(k2_zfmisc_1(A_310, B_309))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.60/2.40  tff(c_2873, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_54, c_2858])).
% 6.60/2.40  tff(c_2880, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_146, c_2873])).
% 6.60/2.40  tff(c_2881, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_2880])).
% 6.60/2.40  tff(c_2893, plain, (![C_312, B_313]: (r2_hidden('#skF_1'(k1_relat_1(C_312), B_313, C_312), k1_relat_1(C_312)) | v1_funct_2(C_312, k1_relat_1(C_312), B_313) | ~v1_funct_1(C_312) | ~v1_relat_1(C_312))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.60/2.40  tff(c_2899, plain, (![B_313]: (r2_hidden('#skF_1'('#skF_3', B_313, '#skF_5'), k1_relat_1('#skF_5')) | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), B_313) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2881, c_2893])).
% 6.60/2.40  tff(c_2917, plain, (![B_315]: (r2_hidden('#skF_1'('#skF_3', B_315, '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', '#skF_3', B_315))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_58, c_2881, c_2881, c_2899])).
% 6.60/2.40  tff(c_2921, plain, (![B_315]: (m1_subset_1('#skF_1'('#skF_3', B_315, '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', '#skF_3', B_315))), inference(resolution, [status(thm)], [c_2917, c_10])).
% 6.60/2.40  tff(c_3274, plain, (![A_358, B_359, C_360, D_361]: (k3_funct_2(A_358, B_359, C_360, D_361)=k1_funct_1(C_360, D_361) | ~m1_subset_1(D_361, A_358) | ~m1_subset_1(C_360, k1_zfmisc_1(k2_zfmisc_1(A_358, B_359))) | ~v1_funct_2(C_360, A_358, B_359) | ~v1_funct_1(C_360) | v1_xboole_0(A_358))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.60/2.40  tff(c_3284, plain, (![B_359, C_360, B_315]: (k3_funct_2('#skF_3', B_359, C_360, '#skF_1'('#skF_3', B_315, '#skF_5'))=k1_funct_1(C_360, '#skF_1'('#skF_3', B_315, '#skF_5')) | ~m1_subset_1(C_360, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_359))) | ~v1_funct_2(C_360, '#skF_3', B_359) | ~v1_funct_1(C_360) | v1_xboole_0('#skF_3') | v1_funct_2('#skF_5', '#skF_3', B_315))), inference(resolution, [status(thm)], [c_2921, c_3274])).
% 6.60/2.40  tff(c_3559, plain, (![B_383, C_384, B_385]: (k3_funct_2('#skF_3', B_383, C_384, '#skF_1'('#skF_3', B_385, '#skF_5'))=k1_funct_1(C_384, '#skF_1'('#skF_3', B_385, '#skF_5')) | ~m1_subset_1(C_384, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_383))) | ~v1_funct_2(C_384, '#skF_3', B_383) | ~v1_funct_1(C_384) | v1_funct_2('#skF_5', '#skF_3', B_385))), inference(negUnitSimplification, [status(thm)], [c_62, c_3284])).
% 6.60/2.40  tff(c_3572, plain, (![B_385]: (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', B_385, '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_385, '#skF_5')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_funct_2('#skF_5', '#skF_3', B_385))), inference(resolution, [status(thm)], [c_54, c_3559])).
% 6.60/2.40  tff(c_4473, plain, (![B_467]: (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', B_467, '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_467, '#skF_5')) | v1_funct_2('#skF_5', '#skF_3', B_467))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_3572])).
% 6.60/2.40  tff(c_4559, plain, (![B_480]: (r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_480, '#skF_5')), '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', B_480, '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', '#skF_3', B_480))), inference(superposition, [status(thm), theory('equality')], [c_4473, c_52])).
% 6.60/2.40  tff(c_2967, plain, (![C_324, B_325]: (~r2_hidden(k1_funct_1(C_324, '#skF_1'(k1_relat_1(C_324), B_325, C_324)), B_325) | v1_funct_2(C_324, k1_relat_1(C_324), B_325) | ~v1_funct_1(C_324) | ~v1_relat_1(C_324))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.60/2.40  tff(c_2970, plain, (![B_325]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_325, '#skF_5')), B_325) | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), B_325) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2881, c_2967])).
% 6.60/2.40  tff(c_2972, plain, (![B_325]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_325, '#skF_5')), B_325) | v1_funct_2('#skF_5', '#skF_3', B_325))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_58, c_2881, c_2970])).
% 6.60/2.40  tff(c_4572, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_4559, c_2972])).
% 6.60/2.40  tff(c_4574, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_4572])).
% 6.60/2.40  tff(c_3067, plain, (![C_335, B_336]: (r2_hidden('#skF_1'(k1_relat_1(C_335), B_336, C_335), k1_relat_1(C_335)) | m1_subset_1(C_335, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_335), B_336))) | ~v1_funct_1(C_335) | ~v1_relat_1(C_335))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.60/2.40  tff(c_3073, plain, (![B_336]: (r2_hidden('#skF_1'('#skF_3', B_336, '#skF_5'), k1_relat_1('#skF_5')) | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), B_336))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2881, c_3067])).
% 6.60/2.40  tff(c_3159, plain, (![B_348]: (r2_hidden('#skF_1'('#skF_3', B_348, '#skF_5'), '#skF_3') | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_348))))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_58, c_2881, c_2881, c_3073])).
% 6.60/2.40  tff(c_3174, plain, (![B_348]: (k2_relset_1('#skF_3', B_348, '#skF_5')=k2_relat_1('#skF_5') | r2_hidden('#skF_1'('#skF_3', B_348, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_3159, c_22])).
% 6.60/2.40  tff(c_3211, plain, (![B_353]: (k2_relset_1('#skF_3', B_353, '#skF_5')='#skF_4' | r2_hidden('#skF_1'('#skF_3', B_353, '#skF_5'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2659, c_3174])).
% 6.60/2.40  tff(c_3215, plain, (![B_353]: (m1_subset_1('#skF_1'('#skF_3', B_353, '#skF_5'), '#skF_3') | k2_relset_1('#skF_3', B_353, '#skF_5')='#skF_4')), inference(resolution, [status(thm)], [c_3211, c_10])).
% 6.60/2.40  tff(c_4584, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_3215, c_4574])).
% 6.60/2.40  tff(c_3243, plain, (![B_357]: (r1_tarski(k2_relset_1('#skF_3', B_357, '#skF_5'), B_357) | r2_hidden('#skF_1'('#skF_3', B_357, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_3159, c_254])).
% 6.60/2.40  tff(c_3273, plain, (![B_357]: (m1_subset_1('#skF_1'('#skF_3', B_357, '#skF_5'), '#skF_3') | r1_tarski(k2_relset_1('#skF_3', B_357, '#skF_5'), B_357))), inference(resolution, [status(thm)], [c_3243, c_10])).
% 6.60/2.40  tff(c_4597, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3') | r1_tarski('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4584, c_3273])).
% 6.60/2.40  tff(c_4612, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2663, c_4574, c_4597])).
% 6.60/2.40  tff(c_4614, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(splitRight, [status(thm)], [c_4572])).
% 6.60/2.40  tff(c_4631, plain, (![B_24, C_25]: (k3_funct_2('#skF_3', B_24, C_25, '#skF_1'('#skF_3', '#skF_2', '#skF_5'))=k1_funct_1(C_25, '#skF_1'('#skF_3', '#skF_2', '#skF_5')) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_24))) | ~v1_funct_2(C_25, '#skF_3', B_24) | ~v1_funct_1(C_25) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_4614, c_36])).
% 6.60/2.40  tff(c_4671, plain, (![B_485, C_486]: (k3_funct_2('#skF_3', B_485, C_486, '#skF_1'('#skF_3', '#skF_2', '#skF_5'))=k1_funct_1(C_486, '#skF_1'('#skF_3', '#skF_2', '#skF_5')) | ~m1_subset_1(C_486, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_485))) | ~v1_funct_2(C_486, '#skF_3', B_485) | ~v1_funct_1(C_486))), inference(negUnitSimplification, [status(thm)], [c_62, c_4631])).
% 6.60/2.40  tff(c_4700, plain, (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_4671])).
% 6.60/2.40  tff(c_4714, plain, (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_4700])).
% 6.60/2.40  tff(c_4724, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5')), '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4714, c_52])).
% 6.60/2.40  tff(c_4735, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4614, c_4724])).
% 6.60/2.40  tff(c_3205, plain, (![C_351, B_352]: (~r2_hidden(k1_funct_1(C_351, '#skF_1'(k1_relat_1(C_351), B_352, C_351)), B_352) | m1_subset_1(C_351, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_351), B_352))) | ~v1_funct_1(C_351) | ~v1_relat_1(C_351))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.60/2.40  tff(c_3208, plain, (![B_352]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_352, '#skF_5')), B_352) | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), B_352))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2881, c_3205])).
% 6.60/2.40  tff(c_3210, plain, (![B_352]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_352, '#skF_5')), B_352) | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_352))))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_58, c_2881, c_3208])).
% 6.60/2.40  tff(c_4751, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_4735, c_3210])).
% 6.60/2.40  tff(c_4782, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_4751, c_22])).
% 6.60/2.40  tff(c_4818, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2659, c_4782])).
% 6.60/2.40  tff(c_18, plain, (![A_11, B_12, C_13]: (m1_subset_1(k2_relset_1(A_11, B_12, C_13), k1_zfmisc_1(B_12)) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.60/2.40  tff(c_4841, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_4818, c_18])).
% 6.60/2.40  tff(c_4851, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4751, c_4841])).
% 6.60/2.40  tff(c_4873, plain, (r1_tarski('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_4851, c_12])).
% 6.60/2.40  tff(c_4878, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2663, c_4873])).
% 6.60/2.40  tff(c_4879, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_2880])).
% 6.60/2.40  tff(c_4892, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_4879, c_8])).
% 6.60/2.40  tff(c_4899, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4892, c_2663])).
% 6.60/2.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.60/2.40  
% 6.60/2.40  Inference rules
% 6.60/2.40  ----------------------
% 6.60/2.40  #Ref     : 0
% 6.60/2.40  #Sup     : 995
% 6.60/2.40  #Fact    : 0
% 6.60/2.40  #Define  : 0
% 6.60/2.40  #Split   : 16
% 6.60/2.40  #Chain   : 0
% 6.60/2.40  #Close   : 0
% 6.60/2.40  
% 6.60/2.40  Ordering : KBO
% 6.60/2.40  
% 6.60/2.40  Simplification rules
% 6.60/2.40  ----------------------
% 6.60/2.40  #Subsume      : 86
% 6.60/2.40  #Demod        : 688
% 6.60/2.40  #Tautology    : 334
% 6.60/2.40  #SimpNegUnit  : 37
% 6.60/2.40  #BackRed      : 50
% 6.60/2.40  
% 6.60/2.40  #Partial instantiations: 0
% 6.60/2.40  #Strategies tried      : 1
% 6.60/2.40  
% 6.60/2.40  Timing (in seconds)
% 6.60/2.40  ----------------------
% 6.60/2.41  Preprocessing        : 0.38
% 6.60/2.41  Parsing              : 0.16
% 6.60/2.41  CNF conversion       : 0.03
% 6.60/2.41  Main loop            : 1.15
% 6.60/2.41  Inferencing          : 0.41
% 6.60/2.41  Reduction            : 0.39
% 6.60/2.41  Demodulation         : 0.27
% 6.60/2.41  BG Simplification    : 0.06
% 6.60/2.41  Subsumption          : 0.19
% 6.60/2.41  Abstraction          : 0.08
% 6.60/2.41  MUC search           : 0.00
% 6.60/2.41  Cooper               : 0.00
% 6.60/2.41  Total                : 1.61
% 6.60/2.41  Index Insertion      : 0.00
% 6.60/2.41  Index Deletion       : 0.00
% 6.60/2.41  Index Matching       : 0.00
% 6.60/2.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
