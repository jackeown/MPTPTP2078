%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:33 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 114 expanded)
%              Number of leaves         :   37 (  56 expanded)
%              Depth                    :   12
%              Number of atoms          :  131 ( 284 expanded)
%              Number of equality atoms :   34 (  66 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_167,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
               => ! [D] :
                    ( m1_subset_1(D,A)
                   => k7_partfun1(B,C,D) = k3_funct_2(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_2)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_123,axiom,(
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

tff(f_134,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_147,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_60,plain,(
    m1_subset_1('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_270,plain,(
    ! [C_93,B_94,A_95] :
      ( v5_relat_1(C_93,B_94)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_95,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_289,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_270])).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( r2_hidden(A_11,B_12)
      | v1_xboole_0(B_12)
      | ~ m1_subset_1(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_137,plain,(
    ! [C_72,A_73,B_74] :
      ( v1_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_154,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_137])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_411,plain,(
    ! [A_127,B_128,C_129] :
      ( k1_relset_1(A_127,B_128,C_129) = k1_relat_1(C_129)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_430,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_411])).

tff(c_848,plain,(
    ! [B_183,A_184,C_185] :
      ( k1_xboole_0 = B_183
      | k1_relset_1(A_184,B_183,C_185) = A_184
      | ~ v1_funct_2(C_185,A_184,B_183)
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(A_184,B_183))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_859,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_848])).

tff(c_874,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_430,c_859])).

tff(c_878,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_874])).

tff(c_964,plain,(
    ! [A_194,B_195,C_196] :
      ( k7_partfun1(A_194,B_195,C_196) = k1_funct_1(B_195,C_196)
      | ~ r2_hidden(C_196,k1_relat_1(B_195))
      | ~ v1_funct_1(B_195)
      | ~ v5_relat_1(B_195,A_194)
      | ~ v1_relat_1(B_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_966,plain,(
    ! [A_194,C_196] :
      ( k7_partfun1(A_194,'#skF_4',C_196) = k1_funct_1('#skF_4',C_196)
      | ~ r2_hidden(C_196,'#skF_2')
      | ~ v1_funct_1('#skF_4')
      | ~ v5_relat_1('#skF_4',A_194)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_878,c_964])).

tff(c_1067,plain,(
    ! [A_210,C_211] :
      ( k7_partfun1(A_210,'#skF_4',C_211) = k1_funct_1('#skF_4',C_211)
      | ~ r2_hidden(C_211,'#skF_2')
      | ~ v5_relat_1('#skF_4',A_210) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_66,c_966])).

tff(c_1070,plain,(
    ! [A_210,A_11] :
      ( k7_partfun1(A_210,'#skF_4',A_11) = k1_funct_1('#skF_4',A_11)
      | ~ v5_relat_1('#skF_4',A_210)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_11,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_1067])).

tff(c_1098,plain,(
    ! [A_216,A_217] :
      ( k7_partfun1(A_216,'#skF_4',A_217) = k1_funct_1('#skF_4',A_217)
      | ~ v5_relat_1('#skF_4',A_216)
      | ~ m1_subset_1(A_217,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1070])).

tff(c_1106,plain,(
    ! [A_218] :
      ( k7_partfun1('#skF_3','#skF_4',A_218) = k1_funct_1('#skF_4',A_218)
      | ~ m1_subset_1(A_218,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_289,c_1098])).

tff(c_1115,plain,(
    k7_partfun1('#skF_3','#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_1106])).

tff(c_58,plain,(
    k3_funct_2('#skF_2','#skF_3','#skF_4','#skF_5') != k7_partfun1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_1116,plain,(
    k3_funct_2('#skF_2','#skF_3','#skF_4','#skF_5') != k1_funct_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1115,c_58])).

tff(c_1039,plain,(
    ! [A_206,B_207,C_208,D_209] :
      ( k3_funct_2(A_206,B_207,C_208,D_209) = k1_funct_1(C_208,D_209)
      | ~ m1_subset_1(D_209,A_206)
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(A_206,B_207)))
      | ~ v1_funct_2(C_208,A_206,B_207)
      | ~ v1_funct_1(C_208)
      | v1_xboole_0(A_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_1053,plain,(
    ! [B_207,C_208] :
      ( k3_funct_2('#skF_2',B_207,C_208,'#skF_5') = k1_funct_1(C_208,'#skF_5')
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_207)))
      | ~ v1_funct_2(C_208,'#skF_2',B_207)
      | ~ v1_funct_1(C_208)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_60,c_1039])).

tff(c_1159,plain,(
    ! [B_224,C_225] :
      ( k3_funct_2('#skF_2',B_224,C_225,'#skF_5') = k1_funct_1(C_225,'#skF_5')
      | ~ m1_subset_1(C_225,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_224)))
      | ~ v1_funct_2(C_225,'#skF_2',B_224)
      | ~ v1_funct_1(C_225) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1053])).

tff(c_1170,plain,
    ( k3_funct_2('#skF_2','#skF_3','#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_5')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_1159])).

tff(c_1183,plain,(
    k3_funct_2('#skF_2','#skF_3','#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1170])).

tff(c_1185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1116,c_1183])).

tff(c_1186,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_874])).

tff(c_12,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_113,plain,(
    ! [A_67,B_68] :
      ( r1_tarski(A_67,B_68)
      | ~ m1_subset_1(A_67,k1_zfmisc_1(B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_122,plain,(
    ! [A_69] : r1_tarski(k1_xboole_0,A_69) ),
    inference(resolution,[status(thm)],[c_12,c_113])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_107,plain,(
    ! [B_64,A_65] :
      ( ~ r1_tarski(B_64,A_65)
      | ~ r2_hidden(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_111,plain,(
    ! [A_1] :
      ( ~ r1_tarski(A_1,'#skF_1'(A_1))
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_107])).

tff(c_127,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_122,c_111])).

tff(c_1215,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1186,c_127])).

tff(c_1222,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1215])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:44:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.53/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.56  
% 3.53/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.56  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 3.53/1.56  
% 3.53/1.56  %Foreground sorts:
% 3.53/1.56  
% 3.53/1.56  
% 3.53/1.56  %Background operators:
% 3.53/1.56  
% 3.53/1.56  
% 3.53/1.56  %Foreground operators:
% 3.53/1.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.53/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.53/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.53/1.56  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.53/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.53/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.53/1.56  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 3.53/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.53/1.56  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.53/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.53/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.53/1.56  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.53/1.56  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.53/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.53/1.56  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.53/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.53/1.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.53/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.53/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.53/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.53/1.56  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.53/1.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.53/1.56  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 3.53/1.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.53/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.53/1.56  
% 3.53/1.58  tff(f_167, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, A) => (k7_partfun1(B, C, D) = k3_funct_2(A, B, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_2)).
% 3.53/1.58  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.53/1.58  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.53/1.58  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.53/1.58  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.53/1.58  tff(f_123, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.53/1.58  tff(f_134, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 3.53/1.58  tff(f_147, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 3.53/1.58  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.53/1.58  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.53/1.58  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.53/1.58  tff(f_71, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.53/1.58  tff(c_68, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.53/1.58  tff(c_60, plain, (m1_subset_1('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.53/1.58  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.53/1.58  tff(c_270, plain, (![C_93, B_94, A_95]: (v5_relat_1(C_93, B_94) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_95, B_94))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.53/1.58  tff(c_289, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_62, c_270])).
% 3.53/1.58  tff(c_70, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.53/1.58  tff(c_16, plain, (![A_11, B_12]: (r2_hidden(A_11, B_12) | v1_xboole_0(B_12) | ~m1_subset_1(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.53/1.58  tff(c_137, plain, (![C_72, A_73, B_74]: (v1_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.53/1.58  tff(c_154, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_137])).
% 3.53/1.58  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.53/1.58  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.53/1.58  tff(c_411, plain, (![A_127, B_128, C_129]: (k1_relset_1(A_127, B_128, C_129)=k1_relat_1(C_129) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.53/1.58  tff(c_430, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_411])).
% 3.53/1.58  tff(c_848, plain, (![B_183, A_184, C_185]: (k1_xboole_0=B_183 | k1_relset_1(A_184, B_183, C_185)=A_184 | ~v1_funct_2(C_185, A_184, B_183) | ~m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1(A_184, B_183))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.53/1.58  tff(c_859, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_62, c_848])).
% 3.53/1.58  tff(c_874, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_430, c_859])).
% 3.53/1.58  tff(c_878, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_874])).
% 3.53/1.58  tff(c_964, plain, (![A_194, B_195, C_196]: (k7_partfun1(A_194, B_195, C_196)=k1_funct_1(B_195, C_196) | ~r2_hidden(C_196, k1_relat_1(B_195)) | ~v1_funct_1(B_195) | ~v5_relat_1(B_195, A_194) | ~v1_relat_1(B_195))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.53/1.58  tff(c_966, plain, (![A_194, C_196]: (k7_partfun1(A_194, '#skF_4', C_196)=k1_funct_1('#skF_4', C_196) | ~r2_hidden(C_196, '#skF_2') | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', A_194) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_878, c_964])).
% 3.53/1.58  tff(c_1067, plain, (![A_210, C_211]: (k7_partfun1(A_210, '#skF_4', C_211)=k1_funct_1('#skF_4', C_211) | ~r2_hidden(C_211, '#skF_2') | ~v5_relat_1('#skF_4', A_210))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_66, c_966])).
% 3.53/1.58  tff(c_1070, plain, (![A_210, A_11]: (k7_partfun1(A_210, '#skF_4', A_11)=k1_funct_1('#skF_4', A_11) | ~v5_relat_1('#skF_4', A_210) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_11, '#skF_2'))), inference(resolution, [status(thm)], [c_16, c_1067])).
% 3.53/1.58  tff(c_1098, plain, (![A_216, A_217]: (k7_partfun1(A_216, '#skF_4', A_217)=k1_funct_1('#skF_4', A_217) | ~v5_relat_1('#skF_4', A_216) | ~m1_subset_1(A_217, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_70, c_1070])).
% 3.53/1.58  tff(c_1106, plain, (![A_218]: (k7_partfun1('#skF_3', '#skF_4', A_218)=k1_funct_1('#skF_4', A_218) | ~m1_subset_1(A_218, '#skF_2'))), inference(resolution, [status(thm)], [c_289, c_1098])).
% 3.53/1.58  tff(c_1115, plain, (k7_partfun1('#skF_3', '#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_60, c_1106])).
% 3.53/1.58  tff(c_58, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k7_partfun1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.53/1.58  tff(c_1116, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k1_funct_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1115, c_58])).
% 3.53/1.58  tff(c_1039, plain, (![A_206, B_207, C_208, D_209]: (k3_funct_2(A_206, B_207, C_208, D_209)=k1_funct_1(C_208, D_209) | ~m1_subset_1(D_209, A_206) | ~m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(A_206, B_207))) | ~v1_funct_2(C_208, A_206, B_207) | ~v1_funct_1(C_208) | v1_xboole_0(A_206))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.53/1.58  tff(c_1053, plain, (![B_207, C_208]: (k3_funct_2('#skF_2', B_207, C_208, '#skF_5')=k1_funct_1(C_208, '#skF_5') | ~m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_207))) | ~v1_funct_2(C_208, '#skF_2', B_207) | ~v1_funct_1(C_208) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_60, c_1039])).
% 3.53/1.58  tff(c_1159, plain, (![B_224, C_225]: (k3_funct_2('#skF_2', B_224, C_225, '#skF_5')=k1_funct_1(C_225, '#skF_5') | ~m1_subset_1(C_225, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_224))) | ~v1_funct_2(C_225, '#skF_2', B_224) | ~v1_funct_1(C_225))), inference(negUnitSimplification, [status(thm)], [c_70, c_1053])).
% 3.53/1.58  tff(c_1170, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_5') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_1159])).
% 3.53/1.58  tff(c_1183, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1170])).
% 3.53/1.58  tff(c_1185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1116, c_1183])).
% 3.53/1.58  tff(c_1186, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_874])).
% 3.53/1.58  tff(c_12, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.53/1.58  tff(c_113, plain, (![A_67, B_68]: (r1_tarski(A_67, B_68) | ~m1_subset_1(A_67, k1_zfmisc_1(B_68)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.53/1.58  tff(c_122, plain, (![A_69]: (r1_tarski(k1_xboole_0, A_69))), inference(resolution, [status(thm)], [c_12, c_113])).
% 3.53/1.58  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.53/1.58  tff(c_107, plain, (![B_64, A_65]: (~r1_tarski(B_64, A_65) | ~r2_hidden(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.53/1.58  tff(c_111, plain, (![A_1]: (~r1_tarski(A_1, '#skF_1'(A_1)) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_107])).
% 3.53/1.58  tff(c_127, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_122, c_111])).
% 3.53/1.58  tff(c_1215, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1186, c_127])).
% 3.53/1.58  tff(c_1222, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_1215])).
% 3.53/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.58  
% 3.53/1.58  Inference rules
% 3.53/1.58  ----------------------
% 3.53/1.58  #Ref     : 0
% 3.53/1.58  #Sup     : 232
% 3.53/1.58  #Fact    : 0
% 3.53/1.58  #Define  : 0
% 3.53/1.58  #Split   : 8
% 3.53/1.58  #Chain   : 0
% 3.53/1.58  #Close   : 0
% 3.53/1.58  
% 3.53/1.58  Ordering : KBO
% 3.53/1.58  
% 3.53/1.58  Simplification rules
% 3.53/1.58  ----------------------
% 3.53/1.58  #Subsume      : 36
% 3.53/1.58  #Demod        : 136
% 3.53/1.58  #Tautology    : 80
% 3.53/1.58  #SimpNegUnit  : 12
% 3.53/1.58  #BackRed      : 36
% 3.53/1.58  
% 3.53/1.58  #Partial instantiations: 0
% 3.53/1.58  #Strategies tried      : 1
% 3.53/1.58  
% 3.53/1.58  Timing (in seconds)
% 3.53/1.58  ----------------------
% 3.53/1.58  Preprocessing        : 0.35
% 3.53/1.58  Parsing              : 0.19
% 3.53/1.58  CNF conversion       : 0.03
% 3.53/1.58  Main loop            : 0.45
% 3.53/1.58  Inferencing          : 0.15
% 3.53/1.58  Reduction            : 0.14
% 3.53/1.58  Demodulation         : 0.10
% 3.53/1.58  BG Simplification    : 0.02
% 3.53/1.58  Subsumption          : 0.09
% 3.53/1.58  Abstraction          : 0.02
% 3.53/1.58  MUC search           : 0.00
% 3.53/1.58  Cooper               : 0.00
% 3.53/1.58  Total                : 0.83
% 3.53/1.58  Index Insertion      : 0.00
% 3.53/1.58  Index Deletion       : 0.00
% 3.53/1.58  Index Matching       : 0.00
% 3.53/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
