%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1048+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:19 EST 2020

% Result     : Theorem 15.89s
% Output     : CNFRefutation 15.89s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 417 expanded)
%              Number of leaves         :   28 ( 160 expanded)
%              Depth                    :   20
%              Number of atoms          :  255 (1504 expanded)
%              Number of equality atoms :    7 (  76 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_relset_1 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k5_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_relset_1,type,(
    r1_relset_1: ( $i * $i * $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( r1_relset_1(A,B,D,C)
             => r1_tarski(k5_partfun1(A,B,C),k5_partfun1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t165_funct_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( D = k5_partfun1(A,B,C)
        <=> ! [E] :
              ( r2_hidden(E,D)
            <=> ? [F] :
                  ( v1_funct_1(F)
                  & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(A,B)))
                  & F = E
                  & v1_partfun1(F,A)
                  & r1_partfun1(C,F) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_partfun1)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ! [E] :
              ( ( v1_relat_1(E)
                & v1_funct_1(E) )
             => ( ( r1_partfun1(C,E)
                  & r1_relset_1(A,B,D,C) )
               => r1_partfun1(D,E) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_partfun1)).

tff(c_48,plain,(
    ~ r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( r2_hidden('#skF_1'(A_4,B_5),A_4)
      | r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_69,plain,(
    ! [A_66,B_67] :
      ( ~ r2_hidden('#skF_1'(A_66,B_67),B_67)
      | r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_74,plain,(
    ! [A_4] : r1_tarski(A_4,A_4) ),
    inference(resolution,[status(thm)],[c_8,c_69])).

tff(c_58,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_56,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_76,plain,(
    ! [C_69,B_70,A_71] :
      ( r2_hidden(C_69,B_70)
      | ~ r2_hidden(C_69,A_71)
      | ~ r1_tarski(A_71,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_79,plain,(
    ! [A_4,B_5,B_70] :
      ( r2_hidden('#skF_1'(A_4,B_5),B_70)
      | ~ r1_tarski(A_4,B_70)
      | r1_tarski(A_4,B_5) ) ),
    inference(resolution,[status(thm)],[c_8,c_76])).

tff(c_93,plain,(
    ! [B_79,C_80,E_81,A_82] :
      ( '#skF_5'(B_79,C_80,E_81,k5_partfun1(A_82,B_79,C_80),A_82) = E_81
      | ~ r2_hidden(E_81,k5_partfun1(A_82,B_79,C_80))
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_82,B_79)))
      | ~ v1_funct_1(C_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_515,plain,(
    ! [B_209,B_210,A_211,C_208,A_212] :
      ( '#skF_5'(B_210,C_208,'#skF_1'(A_212,B_209),k5_partfun1(A_211,B_210,C_208),A_211) = '#skF_1'(A_212,B_209)
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(A_211,B_210)))
      | ~ v1_funct_1(C_208)
      | ~ r1_tarski(A_212,k5_partfun1(A_211,B_210,C_208))
      | r1_tarski(A_212,B_209) ) ),
    inference(resolution,[status(thm)],[c_79,c_93])).

tff(c_521,plain,(
    ! [A_212,B_209] :
      ( '#skF_5'('#skF_7','#skF_8','#skF_1'(A_212,B_209),k5_partfun1('#skF_6','#skF_7','#skF_8'),'#skF_6') = '#skF_1'(A_212,B_209)
      | ~ v1_funct_1('#skF_8')
      | ~ r1_tarski(A_212,k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | r1_tarski(A_212,B_209) ) ),
    inference(resolution,[status(thm)],[c_56,c_515])).

tff(c_532,plain,(
    ! [A_213,B_214] :
      ( '#skF_5'('#skF_7','#skF_8','#skF_1'(A_213,B_214),k5_partfun1('#skF_6','#skF_7','#skF_8'),'#skF_6') = '#skF_1'(A_213,B_214)
      | ~ r1_tarski(A_213,k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | r1_tarski(A_213,B_214) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_521])).

tff(c_102,plain,(
    ! [B_83,C_84,E_85,A_86] :
      ( v1_funct_1('#skF_5'(B_83,C_84,E_85,k5_partfun1(A_86,B_83,C_84),A_86))
      | ~ r2_hidden(E_85,k5_partfun1(A_86,B_83,C_84))
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_86,B_83)))
      | ~ v1_funct_1(C_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_104,plain,(
    ! [E_85] :
      ( v1_funct_1('#skF_5'('#skF_7','#skF_8',E_85,k5_partfun1('#skF_6','#skF_7','#skF_8'),'#skF_6'))
      | ~ r2_hidden(E_85,k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_56,c_102])).

tff(c_109,plain,(
    ! [E_85] :
      ( v1_funct_1('#skF_5'('#skF_7','#skF_8',E_85,k5_partfun1('#skF_6','#skF_7','#skF_8'),'#skF_6'))
      | ~ r2_hidden(E_85,k5_partfun1('#skF_6','#skF_7','#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_104])).

tff(c_588,plain,(
    ! [A_224,B_225] :
      ( v1_funct_1('#skF_1'(A_224,B_225))
      | ~ r2_hidden('#skF_1'(A_224,B_225),k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | ~ r1_tarski(A_224,k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | r1_tarski(A_224,B_225) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_532,c_109])).

tff(c_596,plain,(
    ! [B_5] :
      ( v1_funct_1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),B_5))
      | ~ r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),B_5) ) ),
    inference(resolution,[status(thm)],[c_8,c_588])).

tff(c_600,plain,(
    ! [B_5] :
      ( v1_funct_1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),B_5))
      | r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),B_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_596])).

tff(c_1035,plain,(
    ! [B_296,C_297,A_298,B_299] :
      ( '#skF_5'(B_296,C_297,'#skF_1'(k5_partfun1(A_298,B_296,C_297),B_299),k5_partfun1(A_298,B_296,C_297),A_298) = '#skF_1'(k5_partfun1(A_298,B_296,C_297),B_299)
      | ~ m1_subset_1(C_297,k1_zfmisc_1(k2_zfmisc_1(A_298,B_296)))
      | ~ v1_funct_1(C_297)
      | r1_tarski(k5_partfun1(A_298,B_296,C_297),B_299) ) ),
    inference(resolution,[status(thm)],[c_8,c_93])).

tff(c_12,plain,(
    ! [C_11,B_10,E_47,A_9] :
      ( r1_partfun1(C_11,'#skF_5'(B_10,C_11,E_47,k5_partfun1(A_9,B_10,C_11),A_9))
      | ~ r2_hidden(E_47,k5_partfun1(A_9,B_10,C_11))
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10)))
      | ~ v1_funct_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2353,plain,(
    ! [C_401,A_402,B_403,B_404] :
      ( r1_partfun1(C_401,'#skF_1'(k5_partfun1(A_402,B_403,C_401),B_404))
      | ~ r2_hidden('#skF_1'(k5_partfun1(A_402,B_403,C_401),B_404),k5_partfun1(A_402,B_403,C_401))
      | ~ m1_subset_1(C_401,k1_zfmisc_1(k2_zfmisc_1(A_402,B_403)))
      | ~ v1_funct_1(C_401)
      | ~ m1_subset_1(C_401,k1_zfmisc_1(k2_zfmisc_1(A_402,B_403)))
      | ~ v1_funct_1(C_401)
      | r1_tarski(k5_partfun1(A_402,B_403,C_401),B_404) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1035,c_12])).

tff(c_2357,plain,(
    ! [C_401,A_402,B_403,B_5] :
      ( r1_partfun1(C_401,'#skF_1'(k5_partfun1(A_402,B_403,C_401),B_5))
      | ~ m1_subset_1(C_401,k1_zfmisc_1(k2_zfmisc_1(A_402,B_403)))
      | ~ v1_funct_1(C_401)
      | ~ r1_tarski(k5_partfun1(A_402,B_403,C_401),k5_partfun1(A_402,B_403,C_401))
      | r1_tarski(k5_partfun1(A_402,B_403,C_401),B_5) ) ),
    inference(resolution,[status(thm)],[c_79,c_2353])).

tff(c_2364,plain,(
    ! [C_401,A_402,B_403,B_5] :
      ( r1_partfun1(C_401,'#skF_1'(k5_partfun1(A_402,B_403,C_401),B_5))
      | ~ m1_subset_1(C_401,k1_zfmisc_1(k2_zfmisc_1(A_402,B_403)))
      | ~ v1_funct_1(C_401)
      | r1_tarski(k5_partfun1(A_402,B_403,C_401),B_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2357])).

tff(c_271,plain,(
    ! [B_149,C_150,E_151,A_152] :
      ( m1_subset_1('#skF_5'(B_149,C_150,E_151,k5_partfun1(A_152,B_149,C_150),A_152),k1_zfmisc_1(k2_zfmisc_1(A_152,B_149)))
      | ~ r2_hidden(E_151,k5_partfun1(A_152,B_149,C_150))
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_152,B_149)))
      | ~ v1_funct_1(C_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [C_3,A_1,B_2] :
      ( v1_relat_1(C_3)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_288,plain,(
    ! [B_153,C_154,E_155,A_156] :
      ( v1_relat_1('#skF_5'(B_153,C_154,E_155,k5_partfun1(A_156,B_153,C_154),A_156))
      | ~ r2_hidden(E_155,k5_partfun1(A_156,B_153,C_154))
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_156,B_153)))
      | ~ v1_funct_1(C_154) ) ),
    inference(resolution,[status(thm)],[c_271,c_2])).

tff(c_292,plain,(
    ! [E_155] :
      ( v1_relat_1('#skF_5'('#skF_7','#skF_8',E_155,k5_partfun1('#skF_6','#skF_7','#skF_8'),'#skF_6'))
      | ~ r2_hidden(E_155,k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_56,c_288])).

tff(c_298,plain,(
    ! [E_155] :
      ( v1_relat_1('#skF_5'('#skF_7','#skF_8',E_155,k5_partfun1('#skF_6','#skF_7','#skF_8'),'#skF_6'))
      | ~ r2_hidden(E_155,k5_partfun1('#skF_6','#skF_7','#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_292])).

tff(c_562,plain,(
    ! [A_215,B_216] :
      ( v1_relat_1('#skF_1'(A_215,B_216))
      | ~ r2_hidden('#skF_1'(A_215,B_216),k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | ~ r1_tarski(A_215,k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | r1_tarski(A_215,B_216) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_532,c_298])).

tff(c_570,plain,(
    ! [B_5] :
      ( v1_relat_1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),B_5))
      | ~ r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),B_5) ) ),
    inference(resolution,[status(thm)],[c_8,c_562])).

tff(c_574,plain,(
    ! [B_5] :
      ( v1_relat_1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),B_5))
      | r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),B_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_570])).

tff(c_14,plain,(
    ! [B_10,C_11,E_47,A_9] :
      ( v1_partfun1('#skF_5'(B_10,C_11,E_47,k5_partfun1(A_9,B_10,C_11),A_9),A_9)
      | ~ r2_hidden(E_47,k5_partfun1(A_9,B_10,C_11))
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10)))
      | ~ v1_funct_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_544,plain,(
    ! [A_213,B_214] :
      ( v1_partfun1('#skF_1'(A_213,B_214),'#skF_6')
      | ~ r2_hidden('#skF_1'(A_213,B_214),k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | ~ v1_funct_1('#skF_8')
      | ~ r1_tarski(A_213,k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | r1_tarski(A_213,B_214) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_532,c_14])).

tff(c_726,plain,(
    ! [A_248,B_249] :
      ( v1_partfun1('#skF_1'(A_248,B_249),'#skF_6')
      | ~ r2_hidden('#skF_1'(A_248,B_249),k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | ~ r1_tarski(A_248,k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | r1_tarski(A_248,B_249) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_544])).

tff(c_734,plain,(
    ! [B_5] :
      ( v1_partfun1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),B_5),'#skF_6')
      | ~ r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),B_5) ) ),
    inference(resolution,[status(thm)],[c_8,c_726])).

tff(c_738,plain,(
    ! [B_5] :
      ( v1_partfun1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),B_5),'#skF_6')
      | r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),B_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_734])).

tff(c_54,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_52,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_50,plain,(
    r1_relset_1('#skF_6','#skF_7','#skF_9','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_456,plain,(
    ! [E_197,B_194,D_196,C_195,A_193] :
      ( r1_partfun1(D_196,E_197)
      | ~ r1_relset_1(A_193,B_194,D_196,C_195)
      | ~ r1_partfun1(C_195,E_197)
      | ~ v1_funct_1(E_197)
      | ~ v1_relat_1(E_197)
      | ~ m1_subset_1(D_196,k1_zfmisc_1(k2_zfmisc_1(A_193,B_194)))
      | ~ v1_funct_1(D_196)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(A_193,B_194)))
      | ~ v1_funct_1(C_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_458,plain,(
    ! [E_197] :
      ( r1_partfun1('#skF_9',E_197)
      | ~ r1_partfun1('#skF_8',E_197)
      | ~ v1_funct_1(E_197)
      | ~ v1_relat_1(E_197)
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | ~ v1_funct_1('#skF_9')
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_50,c_456])).

tff(c_461,plain,(
    ! [E_197] :
      ( r1_partfun1('#skF_9',E_197)
      | ~ r1_partfun1('#skF_8',E_197)
      | ~ v1_funct_1(E_197)
      | ~ v1_relat_1(E_197) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_458])).

tff(c_18,plain,(
    ! [B_10,C_11,E_47,A_9] :
      ( m1_subset_1('#skF_5'(B_10,C_11,E_47,k5_partfun1(A_9,B_10,C_11),A_9),k1_zfmisc_1(k2_zfmisc_1(A_9,B_10)))
      | ~ r2_hidden(E_47,k5_partfun1(A_9,B_10,C_11))
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10)))
      | ~ v1_funct_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_541,plain,(
    ! [A_213,B_214] :
      ( m1_subset_1('#skF_1'(A_213,B_214),k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | ~ r2_hidden('#skF_1'(A_213,B_214),k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | ~ v1_funct_1('#skF_8')
      | ~ r1_tarski(A_213,k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | r1_tarski(A_213,B_214) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_532,c_18])).

tff(c_938,plain,(
    ! [A_284,B_285] :
      ( m1_subset_1('#skF_1'(A_284,B_285),k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | ~ r2_hidden('#skF_1'(A_284,B_285),k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | ~ r1_tarski(A_284,k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | r1_tarski(A_284,B_285) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_541])).

tff(c_10,plain,(
    ! [F_50,A_9,B_10,C_11] :
      ( r2_hidden(F_50,k5_partfun1(A_9,B_10,C_11))
      | ~ r1_partfun1(C_11,F_50)
      | ~ v1_partfun1(F_50,A_9)
      | ~ m1_subset_1(F_50,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10)))
      | ~ v1_funct_1(F_50)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10)))
      | ~ v1_funct_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_34576,plain,(
    ! [A_1319,B_1320,C_1321] :
      ( r2_hidden('#skF_1'(A_1319,B_1320),k5_partfun1('#skF_6','#skF_7',C_1321))
      | ~ r1_partfun1(C_1321,'#skF_1'(A_1319,B_1320))
      | ~ v1_partfun1('#skF_1'(A_1319,B_1320),'#skF_6')
      | ~ v1_funct_1('#skF_1'(A_1319,B_1320))
      | ~ m1_subset_1(C_1321,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | ~ v1_funct_1(C_1321)
      | ~ r2_hidden('#skF_1'(A_1319,B_1320),k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | ~ r1_tarski(A_1319,k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | r1_tarski(A_1319,B_1320) ) ),
    inference(resolution,[status(thm)],[c_938,c_10])).

tff(c_34593,plain,(
    ! [A_1322,B_1323,C_1324] :
      ( r2_hidden('#skF_1'(A_1322,B_1323),k5_partfun1('#skF_6','#skF_7',C_1324))
      | ~ r1_partfun1(C_1324,'#skF_1'(A_1322,B_1323))
      | ~ v1_partfun1('#skF_1'(A_1322,B_1323),'#skF_6')
      | ~ v1_funct_1('#skF_1'(A_1322,B_1323))
      | ~ m1_subset_1(C_1324,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | ~ v1_funct_1(C_1324)
      | ~ r1_tarski(A_1322,k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | r1_tarski(A_1322,B_1323) ) ),
    inference(resolution,[status(thm)],[c_79,c_34576])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( ~ r2_hidden('#skF_1'(A_4,B_5),B_5)
      | r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_34615,plain,(
    ! [C_1329,A_1330] :
      ( ~ r1_partfun1(C_1329,'#skF_1'(A_1330,k5_partfun1('#skF_6','#skF_7',C_1329)))
      | ~ v1_partfun1('#skF_1'(A_1330,k5_partfun1('#skF_6','#skF_7',C_1329)),'#skF_6')
      | ~ v1_funct_1('#skF_1'(A_1330,k5_partfun1('#skF_6','#skF_7',C_1329)))
      | ~ m1_subset_1(C_1329,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | ~ v1_funct_1(C_1329)
      | ~ r1_tarski(A_1330,k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | r1_tarski(A_1330,k5_partfun1('#skF_6','#skF_7',C_1329)) ) ),
    inference(resolution,[status(thm)],[c_34593,c_6])).

tff(c_34633,plain,(
    ! [A_1330] :
      ( ~ v1_partfun1('#skF_1'(A_1330,k5_partfun1('#skF_6','#skF_7','#skF_9')),'#skF_6')
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | ~ v1_funct_1('#skF_9')
      | ~ r1_tarski(A_1330,k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | r1_tarski(A_1330,k5_partfun1('#skF_6','#skF_7','#skF_9'))
      | ~ r1_partfun1('#skF_8','#skF_1'(A_1330,k5_partfun1('#skF_6','#skF_7','#skF_9')))
      | ~ v1_funct_1('#skF_1'(A_1330,k5_partfun1('#skF_6','#skF_7','#skF_9')))
      | ~ v1_relat_1('#skF_1'(A_1330,k5_partfun1('#skF_6','#skF_7','#skF_9'))) ) ),
    inference(resolution,[status(thm)],[c_461,c_34615])).

tff(c_34650,plain,(
    ! [A_1331] :
      ( ~ v1_partfun1('#skF_1'(A_1331,k5_partfun1('#skF_6','#skF_7','#skF_9')),'#skF_6')
      | ~ r1_tarski(A_1331,k5_partfun1('#skF_6','#skF_7','#skF_8'))
      | r1_tarski(A_1331,k5_partfun1('#skF_6','#skF_7','#skF_9'))
      | ~ r1_partfun1('#skF_8','#skF_1'(A_1331,k5_partfun1('#skF_6','#skF_7','#skF_9')))
      | ~ v1_funct_1('#skF_1'(A_1331,k5_partfun1('#skF_6','#skF_7','#skF_9')))
      | ~ v1_relat_1('#skF_1'(A_1331,k5_partfun1('#skF_6','#skF_7','#skF_9'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_34633])).

tff(c_34674,plain,
    ( ~ r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_8'))
    | ~ r1_partfun1('#skF_8','#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')))
    | ~ v1_funct_1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')))
    | ~ v1_relat_1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')))
    | r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')) ),
    inference(resolution,[status(thm)],[c_738,c_34650])).

tff(c_34687,plain,
    ( ~ r1_partfun1('#skF_8','#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')))
    | ~ v1_funct_1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')))
    | ~ v1_relat_1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')))
    | r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_34674])).

tff(c_34688,plain,
    ( ~ r1_partfun1('#skF_8','#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')))
    | ~ v1_funct_1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')))
    | ~ v1_relat_1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9'))) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_34687])).

tff(c_34690,plain,(
    ~ v1_relat_1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_34688])).

tff(c_34693,plain,(
    r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')) ),
    inference(resolution,[status(thm)],[c_574,c_34690])).

tff(c_34697,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_34693])).

tff(c_34698,plain,
    ( ~ v1_funct_1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')))
    | ~ r1_partfun1('#skF_8','#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_34688])).

tff(c_34700,plain,(
    ~ r1_partfun1('#skF_8','#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_34698])).

tff(c_34703,plain,
    ( ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
    | ~ v1_funct_1('#skF_8')
    | r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')) ),
    inference(resolution,[status(thm)],[c_2364,c_34700])).

tff(c_34709,plain,(
    r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_34703])).

tff(c_34711,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_34709])).

tff(c_34712,plain,(
    ~ v1_funct_1('#skF_1'(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_34698])).

tff(c_34716,plain,(
    r1_tarski(k5_partfun1('#skF_6','#skF_7','#skF_8'),k5_partfun1('#skF_6','#skF_7','#skF_9')) ),
    inference(resolution,[status(thm)],[c_600,c_34712])).

tff(c_34720,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_34716])).

%------------------------------------------------------------------------------
