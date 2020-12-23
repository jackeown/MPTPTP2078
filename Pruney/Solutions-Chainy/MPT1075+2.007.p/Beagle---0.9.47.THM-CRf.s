%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:11 EST 2020

% Result     : Theorem 7.71s
% Output     : CNFRefutation 7.71s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 454 expanded)
%              Number of leaves         :   50 ( 183 expanded)
%              Depth                    :   14
%              Number of atoms          :  354 (1922 expanded)
%              Number of equality atoms :   59 ( 283 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_202,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C,D] :
                ( ( v1_funct_1(D)
                  & v1_funct_2(D,B,A)
                  & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
               => ! [E] :
                    ( ( v1_funct_1(E)
                      & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C))) )
                   => ! [F] :
                        ( m1_subset_1(F,B)
                       => ( v1_partfun1(E,A)
                         => k3_funct_2(B,C,k8_funct_2(B,A,C,D,E),F) = k1_funct_1(E,k3_funct_2(B,A,D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_funct_2)).

tff(f_73,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_156,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,C)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ! [E] :
              ( ( v1_funct_1(E)
                & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
             => ! [F] :
                  ( m1_subset_1(F,B)
                 => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                   => ( B = k1_xboole_0
                      | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k1_funct_1(E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_81,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_132,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_175,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( m1_subset_1(C,A)
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,A,B)
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
                 => r2_hidden(k3_funct_2(A,B,D,C),k2_relset_1(A,B,D)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_funct_2)).

tff(f_76,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(B))
         => v5_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_relat_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_119,axiom,(
    ! [A,B,C,D,E] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
     => ( v1_funct_1(k8_funct_2(A,B,C,D,E))
        & v1_funct_2(k8_funct_2(A,B,C,D,E),A,C)
        & m1_subset_1(k8_funct_2(A,B,C,D,E),k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_funct_2)).

tff(c_68,plain,(
    m1_subset_1('#skF_8','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_32,plain,(
    ! [A_22,B_23] : v1_relat_1(k2_zfmisc_1(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_74,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_124,plain,(
    ! [B_116,A_117] :
      ( v1_relat_1(B_116)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(A_117))
      | ~ v1_relat_1(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_127,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_74,c_124])).

tff(c_137,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_127])).

tff(c_200,plain,(
    ! [C_133,B_134,A_135] :
      ( v5_relat_1(C_133,B_134)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_135,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_217,plain,(
    v5_relat_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_200])).

tff(c_30,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k2_relat_1(B_21),A_20)
      | ~ v5_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_82,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_78,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_76,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_498,plain,(
    ! [A_175,B_176,C_177] :
      ( k2_relset_1(A_175,B_176,C_177) = k2_relat_1(C_177)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(A_175,B_176))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_515,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_498])).

tff(c_1303,plain,(
    ! [A_258,E_256,F_254,D_255,C_257,B_253] :
      ( k1_funct_1(k8_funct_2(B_253,C_257,A_258,D_255,E_256),F_254) = k1_funct_1(E_256,k1_funct_1(D_255,F_254))
      | k1_xboole_0 = B_253
      | ~ r1_tarski(k2_relset_1(B_253,C_257,D_255),k1_relset_1(C_257,A_258,E_256))
      | ~ m1_subset_1(F_254,B_253)
      | ~ m1_subset_1(E_256,k1_zfmisc_1(k2_zfmisc_1(C_257,A_258)))
      | ~ v1_funct_1(E_256)
      | ~ m1_subset_1(D_255,k1_zfmisc_1(k2_zfmisc_1(B_253,C_257)))
      | ~ v1_funct_2(D_255,B_253,C_257)
      | ~ v1_funct_1(D_255)
      | v1_xboole_0(C_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_1317,plain,(
    ! [A_258,E_256,F_254] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_3',A_258,'#skF_6',E_256),F_254) = k1_funct_1(E_256,k1_funct_1('#skF_6',F_254))
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relset_1('#skF_3',A_258,E_256))
      | ~ m1_subset_1(F_254,'#skF_4')
      | ~ m1_subset_1(E_256,k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_258)))
      | ~ v1_funct_1(E_256)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_515,c_1303])).

tff(c_1338,plain,(
    ! [A_258,E_256,F_254] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_3',A_258,'#skF_6',E_256),F_254) = k1_funct_1(E_256,k1_funct_1('#skF_6',F_254))
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relset_1('#skF_3',A_258,E_256))
      | ~ m1_subset_1(F_254,'#skF_4')
      | ~ m1_subset_1(E_256,k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_258)))
      | ~ v1_funct_1(E_256)
      | v1_xboole_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_1317])).

tff(c_1339,plain,(
    ! [A_258,E_256,F_254] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_3',A_258,'#skF_6',E_256),F_254) = k1_funct_1(E_256,k1_funct_1('#skF_6',F_254))
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relset_1('#skF_3',A_258,E_256))
      | ~ m1_subset_1(F_254,'#skF_4')
      | ~ m1_subset_1(E_256,k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_258)))
      | ~ v1_funct_1(E_256) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_1338])).

tff(c_1388,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1339])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_189,plain,(
    ! [C_128,B_129,A_130] :
      ( r2_hidden(C_128,B_129)
      | ~ r2_hidden(C_128,A_130)
      | ~ r1_tarski(A_130,B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_590,plain,(
    ! [A_189,B_190,B_191] :
      ( r2_hidden('#skF_1'(A_189,B_190),B_191)
      | ~ r1_tarski(A_189,B_191)
      | r1_tarski(A_189,B_190) ) ),
    inference(resolution,[status(thm)],[c_6,c_189])).

tff(c_38,plain,(
    ! [B_25,A_24] :
      ( ~ r1_tarski(B_25,A_24)
      | ~ r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_623,plain,(
    ! [B_197,A_198,B_199] :
      ( ~ r1_tarski(B_197,'#skF_1'(A_198,B_199))
      | ~ r1_tarski(A_198,B_197)
      | r1_tarski(A_198,B_199) ) ),
    inference(resolution,[status(thm)],[c_590,c_38])).

tff(c_639,plain,(
    ! [A_200,B_201] :
      ( ~ r1_tarski(A_200,k1_xboole_0)
      | r1_tarski(A_200,B_201) ) ),
    inference(resolution,[status(thm)],[c_14,c_623])).

tff(c_649,plain,(
    ! [B_21,B_201] :
      ( r1_tarski(k2_relat_1(B_21),B_201)
      | ~ v5_relat_1(B_21,k1_xboole_0)
      | ~ v1_relat_1(B_21) ) ),
    inference(resolution,[status(thm)],[c_30,c_639])).

tff(c_80,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_532,plain,(
    ! [A_180,B_181,C_182,D_183] :
      ( k3_funct_2(A_180,B_181,C_182,D_183) = k1_funct_1(C_182,D_183)
      | ~ m1_subset_1(D_183,A_180)
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(A_180,B_181)))
      | ~ v1_funct_2(C_182,A_180,B_181)
      | ~ v1_funct_1(C_182)
      | v1_xboole_0(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_540,plain,(
    ! [B_181,C_182] :
      ( k3_funct_2('#skF_4',B_181,C_182,'#skF_8') = k1_funct_1(C_182,'#skF_8')
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_181)))
      | ~ v1_funct_2(C_182,'#skF_4',B_181)
      | ~ v1_funct_1(C_182)
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_532])).

tff(c_691,plain,(
    ! [B_204,C_205] :
      ( k3_funct_2('#skF_4',B_204,C_205,'#skF_8') = k1_funct_1(C_205,'#skF_8')
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_204)))
      | ~ v1_funct_2(C_205,'#skF_4',B_204)
      | ~ v1_funct_1(C_205) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_540])).

tff(c_694,plain,
    ( k3_funct_2('#skF_4','#skF_3','#skF_6','#skF_8') = k1_funct_1('#skF_6','#skF_8')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_691])).

tff(c_705,plain,(
    k3_funct_2('#skF_4','#skF_3','#skF_6','#skF_8') = k1_funct_1('#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_694])).

tff(c_991,plain,(
    ! [A_233,B_234,D_235,C_236] :
      ( r2_hidden(k3_funct_2(A_233,B_234,D_235,C_236),k2_relset_1(A_233,B_234,D_235))
      | ~ m1_subset_1(D_235,k1_zfmisc_1(k2_zfmisc_1(A_233,B_234)))
      | ~ v1_funct_2(D_235,A_233,B_234)
      | ~ v1_funct_1(D_235)
      | ~ m1_subset_1(C_236,A_233)
      | v1_xboole_0(B_234)
      | v1_xboole_0(A_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_1002,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_8'),k2_relset_1('#skF_4','#skF_3','#skF_6'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_8','#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_705,c_991])).

tff(c_1020,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_8'),k2_relat_1('#skF_6'))
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_78,c_76,c_74,c_515,c_1002])).

tff(c_1021,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_8'),k2_relat_1('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_82,c_1020])).

tff(c_1038,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),k1_funct_1('#skF_6','#skF_8')) ),
    inference(resolution,[status(thm)],[c_1021,c_38])).

tff(c_1041,plain,
    ( ~ v5_relat_1('#skF_6',k1_xboole_0)
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_649,c_1038])).

tff(c_1047,plain,(
    ~ v5_relat_1('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_1041])).

tff(c_1394,plain,(
    ~ v5_relat_1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1388,c_1047])).

tff(c_34,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1426,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1388,c_1388,c_34])).

tff(c_20,plain,(
    ! [B_10] : k2_zfmisc_1(k1_xboole_0,B_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1422,plain,(
    ! [B_10] : k2_zfmisc_1('#skF_4',B_10) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1388,c_1388,c_20])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_225,plain,(
    ! [B_138,A_139] :
      ( v5_relat_1(B_138,A_139)
      | ~ r1_tarski(k2_relat_1(B_138),A_139)
      | ~ v1_relat_1(B_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_233,plain,(
    ! [B_138] :
      ( v5_relat_1(B_138,k2_relat_1(B_138))
      | ~ v1_relat_1(B_138) ) ),
    inference(resolution,[status(thm)],[c_12,c_225])).

tff(c_355,plain,(
    ! [C_155,A_156,B_157] :
      ( v5_relat_1(C_155,A_156)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(B_157))
      | ~ v5_relat_1(B_157,A_156)
      | ~ v1_relat_1(B_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_357,plain,(
    ! [A_156] :
      ( v5_relat_1('#skF_6',A_156)
      | ~ v5_relat_1(k2_zfmisc_1('#skF_4','#skF_3'),A_156)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_74,c_355])).

tff(c_407,plain,(
    ! [A_164] :
      ( v5_relat_1('#skF_6',A_164)
      | ~ v5_relat_1(k2_zfmisc_1('#skF_4','#skF_3'),A_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_357])).

tff(c_411,plain,
    ( v5_relat_1('#skF_6',k2_relat_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_233,c_407])).

tff(c_414,plain,(
    v5_relat_1('#skF_6',k2_relat_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_411])).

tff(c_1590,plain,(
    v5_relat_1('#skF_6',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1422,c_414])).

tff(c_1593,plain,(
    v5_relat_1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1426,c_1590])).

tff(c_1595,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1394,c_1593])).

tff(c_1597,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1339])).

tff(c_72,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_70,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_130,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_70,c_124])).

tff(c_140,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_130])).

tff(c_66,plain,(
    v1_partfun1('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_295,plain,(
    ! [C_148,A_149,B_150] :
      ( v4_relat_1(C_148,A_149)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_313,plain,(
    v4_relat_1('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_295])).

tff(c_322,plain,(
    ! [B_152,A_153] :
      ( k1_relat_1(B_152) = A_153
      | ~ v1_partfun1(B_152,A_153)
      | ~ v4_relat_1(B_152,A_153)
      | ~ v1_relat_1(B_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_325,plain,
    ( k1_relat_1('#skF_7') = '#skF_3'
    | ~ v1_partfun1('#skF_7','#skF_3')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_313,c_322])).

tff(c_331,plain,(
    k1_relat_1('#skF_7') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_66,c_325])).

tff(c_425,plain,(
    ! [A_165,B_166,C_167] :
      ( k1_relset_1(A_165,B_166,C_167) = k1_relat_1(C_167)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_431,plain,(
    k1_relset_1('#skF_3','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_425])).

tff(c_444,plain,(
    k1_relset_1('#skF_3','#skF_5','#skF_7') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_331,c_431])).

tff(c_1323,plain,(
    ! [B_253,D_255,F_254] :
      ( k1_funct_1(k8_funct_2(B_253,'#skF_3','#skF_5',D_255,'#skF_7'),F_254) = k1_funct_1('#skF_7',k1_funct_1(D_255,F_254))
      | k1_xboole_0 = B_253
      | ~ r1_tarski(k2_relset_1(B_253,'#skF_3',D_255),'#skF_3')
      | ~ m1_subset_1(F_254,B_253)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5')))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(D_255,k1_zfmisc_1(k2_zfmisc_1(B_253,'#skF_3')))
      | ~ v1_funct_2(D_255,B_253,'#skF_3')
      | ~ v1_funct_1(D_255)
      | v1_xboole_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_444,c_1303])).

tff(c_1346,plain,(
    ! [B_253,D_255,F_254] :
      ( k1_funct_1(k8_funct_2(B_253,'#skF_3','#skF_5',D_255,'#skF_7'),F_254) = k1_funct_1('#skF_7',k1_funct_1(D_255,F_254))
      | k1_xboole_0 = B_253
      | ~ r1_tarski(k2_relset_1(B_253,'#skF_3',D_255),'#skF_3')
      | ~ m1_subset_1(F_254,B_253)
      | ~ m1_subset_1(D_255,k1_zfmisc_1(k2_zfmisc_1(B_253,'#skF_3')))
      | ~ v1_funct_2(D_255,B_253,'#skF_3')
      | ~ v1_funct_1(D_255)
      | v1_xboole_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_1323])).

tff(c_1901,plain,(
    ! [B_291,D_292,F_293] :
      ( k1_funct_1(k8_funct_2(B_291,'#skF_3','#skF_5',D_292,'#skF_7'),F_293) = k1_funct_1('#skF_7',k1_funct_1(D_292,F_293))
      | k1_xboole_0 = B_291
      | ~ r1_tarski(k2_relset_1(B_291,'#skF_3',D_292),'#skF_3')
      | ~ m1_subset_1(F_293,B_291)
      | ~ m1_subset_1(D_292,k1_zfmisc_1(k2_zfmisc_1(B_291,'#skF_3')))
      | ~ v1_funct_2(D_292,B_291,'#skF_3')
      | ~ v1_funct_1(D_292) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_1346])).

tff(c_1906,plain,(
    ! [F_293] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_3','#skF_5','#skF_6','#skF_7'),F_293) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_293))
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relset_1('#skF_4','#skF_3','#skF_6'),'#skF_3')
      | ~ m1_subset_1(F_293,'#skF_4')
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_74,c_1901])).

tff(c_1916,plain,(
    ! [F_293] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_3','#skF_5','#skF_6','#skF_7'),F_293) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_293))
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_3')
      | ~ m1_subset_1(F_293,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_515,c_1906])).

tff(c_1917,plain,(
    ! [F_293] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_3','#skF_5','#skF_6','#skF_7'),F_293) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_293))
      | ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_3')
      | ~ m1_subset_1(F_293,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1597,c_1916])).

tff(c_6021,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1917])).

tff(c_6027,plain,
    ( ~ v5_relat_1('#skF_6','#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_30,c_6021])).

tff(c_6034,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_217,c_6027])).

tff(c_6350,plain,(
    ! [F_609] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_3','#skF_5','#skF_6','#skF_7'),F_609) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_609))
      | ~ m1_subset_1(F_609,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_1917])).

tff(c_603,plain,(
    ! [C_196,A_192,D_194,E_195,B_193] :
      ( v1_funct_1(k8_funct_2(A_192,B_193,C_196,D_194,E_195))
      | ~ m1_subset_1(E_195,k1_zfmisc_1(k2_zfmisc_1(B_193,C_196)))
      | ~ v1_funct_1(E_195)
      | ~ m1_subset_1(D_194,k1_zfmisc_1(k2_zfmisc_1(A_192,B_193)))
      | ~ v1_funct_2(D_194,A_192,B_193)
      | ~ v1_funct_1(D_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_607,plain,(
    ! [A_192,D_194] :
      ( v1_funct_1(k8_funct_2(A_192,'#skF_3','#skF_5',D_194,'#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(D_194,k1_zfmisc_1(k2_zfmisc_1(A_192,'#skF_3')))
      | ~ v1_funct_2(D_194,A_192,'#skF_3')
      | ~ v1_funct_1(D_194) ) ),
    inference(resolution,[status(thm)],[c_70,c_603])).

tff(c_1747,plain,(
    ! [A_279,D_280] :
      ( v1_funct_1(k8_funct_2(A_279,'#skF_3','#skF_5',D_280,'#skF_7'))
      | ~ m1_subset_1(D_280,k1_zfmisc_1(k2_zfmisc_1(A_279,'#skF_3')))
      | ~ v1_funct_2(D_280,A_279,'#skF_3')
      | ~ v1_funct_1(D_280) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_607])).

tff(c_1754,plain,
    ( v1_funct_1(k8_funct_2('#skF_4','#skF_3','#skF_5','#skF_6','#skF_7'))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_1747])).

tff(c_1766,plain,(
    v1_funct_1(k8_funct_2('#skF_4','#skF_3','#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_1754])).

tff(c_799,plain,(
    ! [C_216,D_214,B_213,A_212,E_215] :
      ( v1_funct_2(k8_funct_2(A_212,B_213,C_216,D_214,E_215),A_212,C_216)
      | ~ m1_subset_1(E_215,k1_zfmisc_1(k2_zfmisc_1(B_213,C_216)))
      | ~ v1_funct_1(E_215)
      | ~ m1_subset_1(D_214,k1_zfmisc_1(k2_zfmisc_1(A_212,B_213)))
      | ~ v1_funct_2(D_214,A_212,B_213)
      | ~ v1_funct_1(D_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_803,plain,(
    ! [A_212,D_214] :
      ( v1_funct_2(k8_funct_2(A_212,'#skF_3','#skF_5',D_214,'#skF_7'),A_212,'#skF_5')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(D_214,k1_zfmisc_1(k2_zfmisc_1(A_212,'#skF_3')))
      | ~ v1_funct_2(D_214,A_212,'#skF_3')
      | ~ v1_funct_1(D_214) ) ),
    inference(resolution,[status(thm)],[c_70,c_799])).

tff(c_1883,plain,(
    ! [A_289,D_290] :
      ( v1_funct_2(k8_funct_2(A_289,'#skF_3','#skF_5',D_290,'#skF_7'),A_289,'#skF_5')
      | ~ m1_subset_1(D_290,k1_zfmisc_1(k2_zfmisc_1(A_289,'#skF_3')))
      | ~ v1_funct_2(D_290,A_289,'#skF_3')
      | ~ v1_funct_1(D_290) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_803])).

tff(c_1888,plain,
    ( v1_funct_2(k8_funct_2('#skF_4','#skF_3','#skF_5','#skF_6','#skF_7'),'#skF_4','#skF_5')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_1883])).

tff(c_1898,plain,(
    v1_funct_2(k8_funct_2('#skF_4','#skF_3','#skF_5','#skF_6','#skF_7'),'#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_1888])).

tff(c_1134,plain,(
    ! [E_244,A_241,C_245,D_243,B_242] :
      ( m1_subset_1(k8_funct_2(A_241,B_242,C_245,D_243,E_244),k1_zfmisc_1(k2_zfmisc_1(A_241,C_245)))
      | ~ m1_subset_1(E_244,k1_zfmisc_1(k2_zfmisc_1(B_242,C_245)))
      | ~ v1_funct_1(E_244)
      | ~ m1_subset_1(D_243,k1_zfmisc_1(k2_zfmisc_1(A_241,B_242)))
      | ~ v1_funct_2(D_243,A_241,B_242)
      | ~ v1_funct_1(D_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_546,plain,(
    ! [B_181,C_182] :
      ( k3_funct_2('#skF_4',B_181,C_182,'#skF_8') = k1_funct_1(C_182,'#skF_8')
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_181)))
      | ~ v1_funct_2(C_182,'#skF_4',B_181)
      | ~ v1_funct_1(C_182) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_540])).

tff(c_3061,plain,(
    ! [C_380,B_381,D_382,E_383] :
      ( k3_funct_2('#skF_4',C_380,k8_funct_2('#skF_4',B_381,C_380,D_382,E_383),'#skF_8') = k1_funct_1(k8_funct_2('#skF_4',B_381,C_380,D_382,E_383),'#skF_8')
      | ~ v1_funct_2(k8_funct_2('#skF_4',B_381,C_380,D_382,E_383),'#skF_4',C_380)
      | ~ v1_funct_1(k8_funct_2('#skF_4',B_381,C_380,D_382,E_383))
      | ~ m1_subset_1(E_383,k1_zfmisc_1(k2_zfmisc_1(B_381,C_380)))
      | ~ v1_funct_1(E_383)
      | ~ m1_subset_1(D_382,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_381)))
      | ~ v1_funct_2(D_382,'#skF_4',B_381)
      | ~ v1_funct_1(D_382) ) ),
    inference(resolution,[status(thm)],[c_1134,c_546])).

tff(c_3066,plain,
    ( k3_funct_2('#skF_4','#skF_5',k8_funct_2('#skF_4','#skF_3','#skF_5','#skF_6','#skF_7'),'#skF_8') = k1_funct_1(k8_funct_2('#skF_4','#skF_3','#skF_5','#skF_6','#skF_7'),'#skF_8')
    | ~ v1_funct_1(k8_funct_2('#skF_4','#skF_3','#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5')))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1898,c_3061])).

tff(c_3071,plain,(
    k3_funct_2('#skF_4','#skF_5',k8_funct_2('#skF_4','#skF_3','#skF_5','#skF_6','#skF_7'),'#skF_8') = k1_funct_1(k8_funct_2('#skF_4','#skF_3','#skF_5','#skF_6','#skF_7'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_72,c_70,c_1766,c_3066])).

tff(c_64,plain,(
    k3_funct_2('#skF_4','#skF_5',k8_funct_2('#skF_4','#skF_3','#skF_5','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k3_funct_2('#skF_4','#skF_3','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_707,plain,(
    k3_funct_2('#skF_4','#skF_5',k8_funct_2('#skF_4','#skF_3','#skF_5','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_705,c_64])).

tff(c_3484,plain,(
    k1_funct_1(k8_funct_2('#skF_4','#skF_3','#skF_5','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3071,c_707])).

tff(c_6365,plain,(
    ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6350,c_3484])).

tff(c_6379,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_6365])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:00:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.71/2.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.71/2.86  
% 7.71/2.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.71/2.86  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_1
% 7.71/2.86  
% 7.71/2.86  %Foreground sorts:
% 7.71/2.86  
% 7.71/2.86  
% 7.71/2.86  %Background operators:
% 7.71/2.86  
% 7.71/2.86  
% 7.71/2.86  %Foreground operators:
% 7.71/2.86  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.71/2.86  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.71/2.86  tff('#skF_2', type, '#skF_2': $i > $i).
% 7.71/2.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.71/2.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.71/2.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.71/2.86  tff('#skF_7', type, '#skF_7': $i).
% 7.71/2.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.71/2.86  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.71/2.86  tff('#skF_5', type, '#skF_5': $i).
% 7.71/2.86  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.71/2.86  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 7.71/2.86  tff('#skF_6', type, '#skF_6': $i).
% 7.71/2.86  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.71/2.86  tff('#skF_3', type, '#skF_3': $i).
% 7.71/2.86  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.71/2.86  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.71/2.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.71/2.86  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.71/2.86  tff('#skF_8', type, '#skF_8': $i).
% 7.71/2.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.71/2.86  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.71/2.86  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.71/2.86  tff('#skF_4', type, '#skF_4': $i).
% 7.71/2.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.71/2.86  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.71/2.86  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.71/2.86  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.71/2.86  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 7.71/2.86  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.71/2.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.71/2.86  
% 7.71/2.88  tff(f_202, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k1_funct_1(E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_funct_2)).
% 7.71/2.88  tff(f_73, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.71/2.88  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.71/2.88  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.71/2.88  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 7.71/2.88  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.71/2.88  tff(f_156, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 7.71/2.88  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.71/2.88  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.71/2.88  tff(f_81, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 7.71/2.88  tff(f_132, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 7.71/2.88  tff(f_175, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, A) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_hidden(k3_funct_2(A, B, D, C), k2_relset_1(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t189_funct_2)).
% 7.71/2.88  tff(f_76, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 7.71/2.88  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.71/2.88  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.71/2.88  tff(f_65, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(B)) => v5_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc6_relat_1)).
% 7.71/2.88  tff(f_103, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 7.71/2.88  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.71/2.88  tff(f_119, axiom, (![A, B, C, D, E]: (((((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(E)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v1_funct_1(k8_funct_2(A, B, C, D, E)) & v1_funct_2(k8_funct_2(A, B, C, D, E), A, C)) & m1_subset_1(k8_funct_2(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(A, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_funct_2)).
% 7.71/2.88  tff(c_68, plain, (m1_subset_1('#skF_8', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_202])).
% 7.71/2.88  tff(c_32, plain, (![A_22, B_23]: (v1_relat_1(k2_zfmisc_1(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.71/2.88  tff(c_74, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_202])).
% 7.71/2.88  tff(c_124, plain, (![B_116, A_117]: (v1_relat_1(B_116) | ~m1_subset_1(B_116, k1_zfmisc_1(A_117)) | ~v1_relat_1(A_117))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.71/2.88  tff(c_127, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_74, c_124])).
% 7.71/2.88  tff(c_137, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_127])).
% 7.71/2.88  tff(c_200, plain, (![C_133, B_134, A_135]: (v5_relat_1(C_133, B_134) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_135, B_134))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.71/2.88  tff(c_217, plain, (v5_relat_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_200])).
% 7.71/2.88  tff(c_30, plain, (![B_21, A_20]: (r1_tarski(k2_relat_1(B_21), A_20) | ~v5_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.71/2.88  tff(c_82, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_202])).
% 7.71/2.88  tff(c_78, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_202])).
% 7.71/2.88  tff(c_76, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_202])).
% 7.71/2.88  tff(c_498, plain, (![A_175, B_176, C_177]: (k2_relset_1(A_175, B_176, C_177)=k2_relat_1(C_177) | ~m1_subset_1(C_177, k1_zfmisc_1(k2_zfmisc_1(A_175, B_176))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.71/2.88  tff(c_515, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_74, c_498])).
% 7.71/2.88  tff(c_1303, plain, (![A_258, E_256, F_254, D_255, C_257, B_253]: (k1_funct_1(k8_funct_2(B_253, C_257, A_258, D_255, E_256), F_254)=k1_funct_1(E_256, k1_funct_1(D_255, F_254)) | k1_xboole_0=B_253 | ~r1_tarski(k2_relset_1(B_253, C_257, D_255), k1_relset_1(C_257, A_258, E_256)) | ~m1_subset_1(F_254, B_253) | ~m1_subset_1(E_256, k1_zfmisc_1(k2_zfmisc_1(C_257, A_258))) | ~v1_funct_1(E_256) | ~m1_subset_1(D_255, k1_zfmisc_1(k2_zfmisc_1(B_253, C_257))) | ~v1_funct_2(D_255, B_253, C_257) | ~v1_funct_1(D_255) | v1_xboole_0(C_257))), inference(cnfTransformation, [status(thm)], [f_156])).
% 7.71/2.88  tff(c_1317, plain, (![A_258, E_256, F_254]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_3', A_258, '#skF_6', E_256), F_254)=k1_funct_1(E_256, k1_funct_1('#skF_6', F_254)) | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relat_1('#skF_6'), k1_relset_1('#skF_3', A_258, E_256)) | ~m1_subset_1(F_254, '#skF_4') | ~m1_subset_1(E_256, k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_258))) | ~v1_funct_1(E_256) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_515, c_1303])).
% 7.71/2.88  tff(c_1338, plain, (![A_258, E_256, F_254]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_3', A_258, '#skF_6', E_256), F_254)=k1_funct_1(E_256, k1_funct_1('#skF_6', F_254)) | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relat_1('#skF_6'), k1_relset_1('#skF_3', A_258, E_256)) | ~m1_subset_1(F_254, '#skF_4') | ~m1_subset_1(E_256, k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_258))) | ~v1_funct_1(E_256) | v1_xboole_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_1317])).
% 7.71/2.88  tff(c_1339, plain, (![A_258, E_256, F_254]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_3', A_258, '#skF_6', E_256), F_254)=k1_funct_1(E_256, k1_funct_1('#skF_6', F_254)) | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relat_1('#skF_6'), k1_relset_1('#skF_3', A_258, E_256)) | ~m1_subset_1(F_254, '#skF_4') | ~m1_subset_1(E_256, k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_258))) | ~v1_funct_1(E_256))), inference(negUnitSimplification, [status(thm)], [c_82, c_1338])).
% 7.71/2.88  tff(c_1388, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_1339])).
% 7.71/2.88  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.71/2.88  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.71/2.88  tff(c_189, plain, (![C_128, B_129, A_130]: (r2_hidden(C_128, B_129) | ~r2_hidden(C_128, A_130) | ~r1_tarski(A_130, B_129))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.71/2.88  tff(c_590, plain, (![A_189, B_190, B_191]: (r2_hidden('#skF_1'(A_189, B_190), B_191) | ~r1_tarski(A_189, B_191) | r1_tarski(A_189, B_190))), inference(resolution, [status(thm)], [c_6, c_189])).
% 7.71/2.88  tff(c_38, plain, (![B_25, A_24]: (~r1_tarski(B_25, A_24) | ~r2_hidden(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.71/2.88  tff(c_623, plain, (![B_197, A_198, B_199]: (~r1_tarski(B_197, '#skF_1'(A_198, B_199)) | ~r1_tarski(A_198, B_197) | r1_tarski(A_198, B_199))), inference(resolution, [status(thm)], [c_590, c_38])).
% 7.71/2.88  tff(c_639, plain, (![A_200, B_201]: (~r1_tarski(A_200, k1_xboole_0) | r1_tarski(A_200, B_201))), inference(resolution, [status(thm)], [c_14, c_623])).
% 7.71/2.88  tff(c_649, plain, (![B_21, B_201]: (r1_tarski(k2_relat_1(B_21), B_201) | ~v5_relat_1(B_21, k1_xboole_0) | ~v1_relat_1(B_21))), inference(resolution, [status(thm)], [c_30, c_639])).
% 7.71/2.88  tff(c_80, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_202])).
% 7.71/2.88  tff(c_532, plain, (![A_180, B_181, C_182, D_183]: (k3_funct_2(A_180, B_181, C_182, D_183)=k1_funct_1(C_182, D_183) | ~m1_subset_1(D_183, A_180) | ~m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1(A_180, B_181))) | ~v1_funct_2(C_182, A_180, B_181) | ~v1_funct_1(C_182) | v1_xboole_0(A_180))), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.71/2.88  tff(c_540, plain, (![B_181, C_182]: (k3_funct_2('#skF_4', B_181, C_182, '#skF_8')=k1_funct_1(C_182, '#skF_8') | ~m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_181))) | ~v1_funct_2(C_182, '#skF_4', B_181) | ~v1_funct_1(C_182) | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_532])).
% 7.71/2.88  tff(c_691, plain, (![B_204, C_205]: (k3_funct_2('#skF_4', B_204, C_205, '#skF_8')=k1_funct_1(C_205, '#skF_8') | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_204))) | ~v1_funct_2(C_205, '#skF_4', B_204) | ~v1_funct_1(C_205))), inference(negUnitSimplification, [status(thm)], [c_80, c_540])).
% 7.71/2.88  tff(c_694, plain, (k3_funct_2('#skF_4', '#skF_3', '#skF_6', '#skF_8')=k1_funct_1('#skF_6', '#skF_8') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_74, c_691])).
% 7.71/2.88  tff(c_705, plain, (k3_funct_2('#skF_4', '#skF_3', '#skF_6', '#skF_8')=k1_funct_1('#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_694])).
% 7.71/2.88  tff(c_991, plain, (![A_233, B_234, D_235, C_236]: (r2_hidden(k3_funct_2(A_233, B_234, D_235, C_236), k2_relset_1(A_233, B_234, D_235)) | ~m1_subset_1(D_235, k1_zfmisc_1(k2_zfmisc_1(A_233, B_234))) | ~v1_funct_2(D_235, A_233, B_234) | ~v1_funct_1(D_235) | ~m1_subset_1(C_236, A_233) | v1_xboole_0(B_234) | v1_xboole_0(A_233))), inference(cnfTransformation, [status(thm)], [f_175])).
% 7.71/2.88  tff(c_1002, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_8'), k2_relset_1('#skF_4', '#skF_3', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_8', '#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_705, c_991])).
% 7.71/2.88  tff(c_1020, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_8'), k2_relat_1('#skF_6')) | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_78, c_76, c_74, c_515, c_1002])).
% 7.71/2.88  tff(c_1021, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_8'), k2_relat_1('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_80, c_82, c_1020])).
% 7.71/2.88  tff(c_1038, plain, (~r1_tarski(k2_relat_1('#skF_6'), k1_funct_1('#skF_6', '#skF_8'))), inference(resolution, [status(thm)], [c_1021, c_38])).
% 7.71/2.88  tff(c_1041, plain, (~v5_relat_1('#skF_6', k1_xboole_0) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_649, c_1038])).
% 7.71/2.88  tff(c_1047, plain, (~v5_relat_1('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_137, c_1041])).
% 7.71/2.88  tff(c_1394, plain, (~v5_relat_1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1388, c_1047])).
% 7.71/2.88  tff(c_34, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.71/2.88  tff(c_1426, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1388, c_1388, c_34])).
% 7.71/2.88  tff(c_20, plain, (![B_10]: (k2_zfmisc_1(k1_xboole_0, B_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.71/2.88  tff(c_1422, plain, (![B_10]: (k2_zfmisc_1('#skF_4', B_10)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1388, c_1388, c_20])).
% 7.71/2.88  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.71/2.88  tff(c_225, plain, (![B_138, A_139]: (v5_relat_1(B_138, A_139) | ~r1_tarski(k2_relat_1(B_138), A_139) | ~v1_relat_1(B_138))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.71/2.88  tff(c_233, plain, (![B_138]: (v5_relat_1(B_138, k2_relat_1(B_138)) | ~v1_relat_1(B_138))), inference(resolution, [status(thm)], [c_12, c_225])).
% 7.71/2.88  tff(c_355, plain, (![C_155, A_156, B_157]: (v5_relat_1(C_155, A_156) | ~m1_subset_1(C_155, k1_zfmisc_1(B_157)) | ~v5_relat_1(B_157, A_156) | ~v1_relat_1(B_157))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.71/2.88  tff(c_357, plain, (![A_156]: (v5_relat_1('#skF_6', A_156) | ~v5_relat_1(k2_zfmisc_1('#skF_4', '#skF_3'), A_156) | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(resolution, [status(thm)], [c_74, c_355])).
% 7.71/2.88  tff(c_407, plain, (![A_164]: (v5_relat_1('#skF_6', A_164) | ~v5_relat_1(k2_zfmisc_1('#skF_4', '#skF_3'), A_164))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_357])).
% 7.71/2.88  tff(c_411, plain, (v5_relat_1('#skF_6', k2_relat_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_233, c_407])).
% 7.71/2.88  tff(c_414, plain, (v5_relat_1('#skF_6', k2_relat_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_411])).
% 7.71/2.88  tff(c_1590, plain, (v5_relat_1('#skF_6', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1422, c_414])).
% 7.71/2.88  tff(c_1593, plain, (v5_relat_1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1426, c_1590])).
% 7.71/2.88  tff(c_1595, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1394, c_1593])).
% 7.71/2.88  tff(c_1597, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_1339])).
% 7.71/2.88  tff(c_72, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_202])).
% 7.71/2.88  tff(c_70, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_202])).
% 7.71/2.88  tff(c_130, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_70, c_124])).
% 7.71/2.88  tff(c_140, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_130])).
% 7.71/2.88  tff(c_66, plain, (v1_partfun1('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_202])).
% 7.71/2.88  tff(c_295, plain, (![C_148, A_149, B_150]: (v4_relat_1(C_148, A_149) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.71/2.88  tff(c_313, plain, (v4_relat_1('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_70, c_295])).
% 7.71/2.88  tff(c_322, plain, (![B_152, A_153]: (k1_relat_1(B_152)=A_153 | ~v1_partfun1(B_152, A_153) | ~v4_relat_1(B_152, A_153) | ~v1_relat_1(B_152))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.71/2.88  tff(c_325, plain, (k1_relat_1('#skF_7')='#skF_3' | ~v1_partfun1('#skF_7', '#skF_3') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_313, c_322])).
% 7.71/2.88  tff(c_331, plain, (k1_relat_1('#skF_7')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_140, c_66, c_325])).
% 7.71/2.88  tff(c_425, plain, (![A_165, B_166, C_167]: (k1_relset_1(A_165, B_166, C_167)=k1_relat_1(C_167) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.71/2.88  tff(c_431, plain, (k1_relset_1('#skF_3', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_70, c_425])).
% 7.71/2.88  tff(c_444, plain, (k1_relset_1('#skF_3', '#skF_5', '#skF_7')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_331, c_431])).
% 7.71/2.88  tff(c_1323, plain, (![B_253, D_255, F_254]: (k1_funct_1(k8_funct_2(B_253, '#skF_3', '#skF_5', D_255, '#skF_7'), F_254)=k1_funct_1('#skF_7', k1_funct_1(D_255, F_254)) | k1_xboole_0=B_253 | ~r1_tarski(k2_relset_1(B_253, '#skF_3', D_255), '#skF_3') | ~m1_subset_1(F_254, B_253) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_5'))) | ~v1_funct_1('#skF_7') | ~m1_subset_1(D_255, k1_zfmisc_1(k2_zfmisc_1(B_253, '#skF_3'))) | ~v1_funct_2(D_255, B_253, '#skF_3') | ~v1_funct_1(D_255) | v1_xboole_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_444, c_1303])).
% 7.71/2.88  tff(c_1346, plain, (![B_253, D_255, F_254]: (k1_funct_1(k8_funct_2(B_253, '#skF_3', '#skF_5', D_255, '#skF_7'), F_254)=k1_funct_1('#skF_7', k1_funct_1(D_255, F_254)) | k1_xboole_0=B_253 | ~r1_tarski(k2_relset_1(B_253, '#skF_3', D_255), '#skF_3') | ~m1_subset_1(F_254, B_253) | ~m1_subset_1(D_255, k1_zfmisc_1(k2_zfmisc_1(B_253, '#skF_3'))) | ~v1_funct_2(D_255, B_253, '#skF_3') | ~v1_funct_1(D_255) | v1_xboole_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_1323])).
% 7.71/2.88  tff(c_1901, plain, (![B_291, D_292, F_293]: (k1_funct_1(k8_funct_2(B_291, '#skF_3', '#skF_5', D_292, '#skF_7'), F_293)=k1_funct_1('#skF_7', k1_funct_1(D_292, F_293)) | k1_xboole_0=B_291 | ~r1_tarski(k2_relset_1(B_291, '#skF_3', D_292), '#skF_3') | ~m1_subset_1(F_293, B_291) | ~m1_subset_1(D_292, k1_zfmisc_1(k2_zfmisc_1(B_291, '#skF_3'))) | ~v1_funct_2(D_292, B_291, '#skF_3') | ~v1_funct_1(D_292))), inference(negUnitSimplification, [status(thm)], [c_82, c_1346])).
% 7.71/2.88  tff(c_1906, plain, (![F_293]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_3', '#skF_5', '#skF_6', '#skF_7'), F_293)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_293)) | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relset_1('#skF_4', '#skF_3', '#skF_6'), '#skF_3') | ~m1_subset_1(F_293, '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_74, c_1901])).
% 7.71/2.88  tff(c_1916, plain, (![F_293]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_3', '#skF_5', '#skF_6', '#skF_7'), F_293)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_293)) | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relat_1('#skF_6'), '#skF_3') | ~m1_subset_1(F_293, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_515, c_1906])).
% 7.71/2.88  tff(c_1917, plain, (![F_293]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_3', '#skF_5', '#skF_6', '#skF_7'), F_293)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_293)) | ~r1_tarski(k2_relat_1('#skF_6'), '#skF_3') | ~m1_subset_1(F_293, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1597, c_1916])).
% 7.71/2.88  tff(c_6021, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1917])).
% 7.71/2.88  tff(c_6027, plain, (~v5_relat_1('#skF_6', '#skF_3') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_30, c_6021])).
% 7.71/2.88  tff(c_6034, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_137, c_217, c_6027])).
% 7.71/2.88  tff(c_6350, plain, (![F_609]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_3', '#skF_5', '#skF_6', '#skF_7'), F_609)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_609)) | ~m1_subset_1(F_609, '#skF_4'))), inference(splitRight, [status(thm)], [c_1917])).
% 7.71/2.88  tff(c_603, plain, (![C_196, A_192, D_194, E_195, B_193]: (v1_funct_1(k8_funct_2(A_192, B_193, C_196, D_194, E_195)) | ~m1_subset_1(E_195, k1_zfmisc_1(k2_zfmisc_1(B_193, C_196))) | ~v1_funct_1(E_195) | ~m1_subset_1(D_194, k1_zfmisc_1(k2_zfmisc_1(A_192, B_193))) | ~v1_funct_2(D_194, A_192, B_193) | ~v1_funct_1(D_194))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.71/2.88  tff(c_607, plain, (![A_192, D_194]: (v1_funct_1(k8_funct_2(A_192, '#skF_3', '#skF_5', D_194, '#skF_7')) | ~v1_funct_1('#skF_7') | ~m1_subset_1(D_194, k1_zfmisc_1(k2_zfmisc_1(A_192, '#skF_3'))) | ~v1_funct_2(D_194, A_192, '#skF_3') | ~v1_funct_1(D_194))), inference(resolution, [status(thm)], [c_70, c_603])).
% 7.71/2.88  tff(c_1747, plain, (![A_279, D_280]: (v1_funct_1(k8_funct_2(A_279, '#skF_3', '#skF_5', D_280, '#skF_7')) | ~m1_subset_1(D_280, k1_zfmisc_1(k2_zfmisc_1(A_279, '#skF_3'))) | ~v1_funct_2(D_280, A_279, '#skF_3') | ~v1_funct_1(D_280))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_607])).
% 7.71/2.88  tff(c_1754, plain, (v1_funct_1(k8_funct_2('#skF_4', '#skF_3', '#skF_5', '#skF_6', '#skF_7')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_74, c_1747])).
% 7.71/2.88  tff(c_1766, plain, (v1_funct_1(k8_funct_2('#skF_4', '#skF_3', '#skF_5', '#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_1754])).
% 7.71/2.88  tff(c_799, plain, (![C_216, D_214, B_213, A_212, E_215]: (v1_funct_2(k8_funct_2(A_212, B_213, C_216, D_214, E_215), A_212, C_216) | ~m1_subset_1(E_215, k1_zfmisc_1(k2_zfmisc_1(B_213, C_216))) | ~v1_funct_1(E_215) | ~m1_subset_1(D_214, k1_zfmisc_1(k2_zfmisc_1(A_212, B_213))) | ~v1_funct_2(D_214, A_212, B_213) | ~v1_funct_1(D_214))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.71/2.88  tff(c_803, plain, (![A_212, D_214]: (v1_funct_2(k8_funct_2(A_212, '#skF_3', '#skF_5', D_214, '#skF_7'), A_212, '#skF_5') | ~v1_funct_1('#skF_7') | ~m1_subset_1(D_214, k1_zfmisc_1(k2_zfmisc_1(A_212, '#skF_3'))) | ~v1_funct_2(D_214, A_212, '#skF_3') | ~v1_funct_1(D_214))), inference(resolution, [status(thm)], [c_70, c_799])).
% 7.71/2.88  tff(c_1883, plain, (![A_289, D_290]: (v1_funct_2(k8_funct_2(A_289, '#skF_3', '#skF_5', D_290, '#skF_7'), A_289, '#skF_5') | ~m1_subset_1(D_290, k1_zfmisc_1(k2_zfmisc_1(A_289, '#skF_3'))) | ~v1_funct_2(D_290, A_289, '#skF_3') | ~v1_funct_1(D_290))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_803])).
% 7.71/2.88  tff(c_1888, plain, (v1_funct_2(k8_funct_2('#skF_4', '#skF_3', '#skF_5', '#skF_6', '#skF_7'), '#skF_4', '#skF_5') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_74, c_1883])).
% 7.71/2.88  tff(c_1898, plain, (v1_funct_2(k8_funct_2('#skF_4', '#skF_3', '#skF_5', '#skF_6', '#skF_7'), '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_1888])).
% 7.71/2.88  tff(c_1134, plain, (![E_244, A_241, C_245, D_243, B_242]: (m1_subset_1(k8_funct_2(A_241, B_242, C_245, D_243, E_244), k1_zfmisc_1(k2_zfmisc_1(A_241, C_245))) | ~m1_subset_1(E_244, k1_zfmisc_1(k2_zfmisc_1(B_242, C_245))) | ~v1_funct_1(E_244) | ~m1_subset_1(D_243, k1_zfmisc_1(k2_zfmisc_1(A_241, B_242))) | ~v1_funct_2(D_243, A_241, B_242) | ~v1_funct_1(D_243))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.71/2.88  tff(c_546, plain, (![B_181, C_182]: (k3_funct_2('#skF_4', B_181, C_182, '#skF_8')=k1_funct_1(C_182, '#skF_8') | ~m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_181))) | ~v1_funct_2(C_182, '#skF_4', B_181) | ~v1_funct_1(C_182))), inference(negUnitSimplification, [status(thm)], [c_80, c_540])).
% 7.71/2.88  tff(c_3061, plain, (![C_380, B_381, D_382, E_383]: (k3_funct_2('#skF_4', C_380, k8_funct_2('#skF_4', B_381, C_380, D_382, E_383), '#skF_8')=k1_funct_1(k8_funct_2('#skF_4', B_381, C_380, D_382, E_383), '#skF_8') | ~v1_funct_2(k8_funct_2('#skF_4', B_381, C_380, D_382, E_383), '#skF_4', C_380) | ~v1_funct_1(k8_funct_2('#skF_4', B_381, C_380, D_382, E_383)) | ~m1_subset_1(E_383, k1_zfmisc_1(k2_zfmisc_1(B_381, C_380))) | ~v1_funct_1(E_383) | ~m1_subset_1(D_382, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_381))) | ~v1_funct_2(D_382, '#skF_4', B_381) | ~v1_funct_1(D_382))), inference(resolution, [status(thm)], [c_1134, c_546])).
% 7.71/2.88  tff(c_3066, plain, (k3_funct_2('#skF_4', '#skF_5', k8_funct_2('#skF_4', '#skF_3', '#skF_5', '#skF_6', '#skF_7'), '#skF_8')=k1_funct_1(k8_funct_2('#skF_4', '#skF_3', '#skF_5', '#skF_6', '#skF_7'), '#skF_8') | ~v1_funct_1(k8_funct_2('#skF_4', '#skF_3', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_5'))) | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_1898, c_3061])).
% 7.71/2.88  tff(c_3071, plain, (k3_funct_2('#skF_4', '#skF_5', k8_funct_2('#skF_4', '#skF_3', '#skF_5', '#skF_6', '#skF_7'), '#skF_8')=k1_funct_1(k8_funct_2('#skF_4', '#skF_3', '#skF_5', '#skF_6', '#skF_7'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_72, c_70, c_1766, c_3066])).
% 7.71/2.88  tff(c_64, plain, (k3_funct_2('#skF_4', '#skF_5', k8_funct_2('#skF_4', '#skF_3', '#skF_5', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k3_funct_2('#skF_4', '#skF_3', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_202])).
% 7.71/2.88  tff(c_707, plain, (k3_funct_2('#skF_4', '#skF_5', k8_funct_2('#skF_4', '#skF_3', '#skF_5', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_705, c_64])).
% 7.71/2.88  tff(c_3484, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_3', '#skF_5', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_3071, c_707])).
% 7.71/2.88  tff(c_6365, plain, (~m1_subset_1('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6350, c_3484])).
% 7.71/2.88  tff(c_6379, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_6365])).
% 7.71/2.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.71/2.88  
% 7.71/2.88  Inference rules
% 7.71/2.88  ----------------------
% 7.71/2.88  #Ref     : 0
% 7.71/2.88  #Sup     : 1317
% 7.71/2.88  #Fact    : 0
% 7.71/2.88  #Define  : 0
% 7.71/2.88  #Split   : 30
% 7.71/2.88  #Chain   : 0
% 7.71/2.88  #Close   : 0
% 7.71/2.88  
% 7.71/2.88  Ordering : KBO
% 7.71/2.88  
% 7.71/2.88  Simplification rules
% 7.71/2.88  ----------------------
% 7.71/2.88  #Subsume      : 481
% 7.71/2.88  #Demod        : 1284
% 7.71/2.88  #Tautology    : 223
% 7.71/2.88  #SimpNegUnit  : 28
% 7.71/2.88  #BackRed      : 48
% 7.71/2.88  
% 7.71/2.88  #Partial instantiations: 0
% 7.71/2.88  #Strategies tried      : 1
% 7.71/2.88  
% 7.71/2.88  Timing (in seconds)
% 7.71/2.88  ----------------------
% 7.71/2.88  Preprocessing        : 0.38
% 7.71/2.88  Parsing              : 0.21
% 7.71/2.88  CNF conversion       : 0.03
% 7.71/2.88  Main loop            : 1.67
% 7.71/2.88  Inferencing          : 0.48
% 7.71/2.88  Reduction            : 0.65
% 7.71/2.89  Demodulation         : 0.46
% 7.71/2.89  BG Simplification    : 0.06
% 7.71/2.89  Subsumption          : 0.36
% 7.71/2.89  Abstraction          : 0.06
% 7.71/2.89  MUC search           : 0.00
% 7.71/2.89  Cooper               : 0.00
% 7.71/2.89  Total                : 2.10
% 7.71/2.89  Index Insertion      : 0.00
% 7.71/2.89  Index Deletion       : 0.00
% 7.71/2.89  Index Matching       : 0.00
% 7.71/2.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
