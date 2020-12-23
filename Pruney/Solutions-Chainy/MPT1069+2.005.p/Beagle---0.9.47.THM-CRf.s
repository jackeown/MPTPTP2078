%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:45 EST 2020

% Result     : Theorem 7.49s
% Output     : CNFRefutation 7.77s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 796 expanded)
%              Number of leaves         :   50 ( 299 expanded)
%              Depth                    :   23
%              Number of atoms          :  355 (3118 expanded)
%              Number of equality atoms :   67 ( 663 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_243,negated_conjecture,(
    ~ ! [A,B,C] :
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
                        | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k7_partfun1(A,E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).

tff(f_111,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_170,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_97,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_218,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r1_tarski(k2_relset_1(A,B,D),C)
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | ( v1_funct_1(D)
            & v1_funct_2(D,A,C)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_199,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_135,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & ~ v1_xboole_0(C)
              & v1_funct_2(C,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_funct_2)).

tff(f_146,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

tff(c_88,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_92,plain,(
    m1_subset_1('#skF_8','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_102,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_100,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_98,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_94,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_459,plain,(
    ! [A_153,B_154,C_155] :
      ( k1_relset_1(A_153,B_154,C_155) = k1_relat_1(C_155)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_477,plain,(
    k1_relset_1('#skF_5','#skF_3','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_94,c_459])).

tff(c_370,plain,(
    ! [A_140,B_141,C_142] :
      ( k2_relset_1(A_140,B_141,C_142) = k2_relat_1(C_142)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_389,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_98,c_370])).

tff(c_90,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_394,plain,(
    r1_tarski(k2_relat_1('#skF_6'),k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_389,c_90])).

tff(c_480,plain,(
    r1_tarski(k2_relat_1('#skF_6'),k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_394])).

tff(c_104,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_96,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_1475,plain,(
    ! [C_277,A_272,B_275,F_274,E_273,D_276] :
      ( k1_funct_1(k8_funct_2(B_275,C_277,A_272,D_276,E_273),F_274) = k1_funct_1(E_273,k1_funct_1(D_276,F_274))
      | k1_xboole_0 = B_275
      | ~ r1_tarski(k2_relset_1(B_275,C_277,D_276),k1_relset_1(C_277,A_272,E_273))
      | ~ m1_subset_1(F_274,B_275)
      | ~ m1_subset_1(E_273,k1_zfmisc_1(k2_zfmisc_1(C_277,A_272)))
      | ~ v1_funct_1(E_273)
      | ~ m1_subset_1(D_276,k1_zfmisc_1(k2_zfmisc_1(B_275,C_277)))
      | ~ v1_funct_2(D_276,B_275,C_277)
      | ~ v1_funct_1(D_276)
      | v1_xboole_0(C_277) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_1483,plain,(
    ! [B_275,D_276,F_274] :
      ( k1_funct_1(k8_funct_2(B_275,'#skF_5','#skF_3',D_276,'#skF_7'),F_274) = k1_funct_1('#skF_7',k1_funct_1(D_276,F_274))
      | k1_xboole_0 = B_275
      | ~ r1_tarski(k2_relset_1(B_275,'#skF_5',D_276),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_274,B_275)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(D_276,k1_zfmisc_1(k2_zfmisc_1(B_275,'#skF_5')))
      | ~ v1_funct_2(D_276,B_275,'#skF_5')
      | ~ v1_funct_1(D_276)
      | v1_xboole_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_477,c_1475])).

tff(c_1495,plain,(
    ! [B_275,D_276,F_274] :
      ( k1_funct_1(k8_funct_2(B_275,'#skF_5','#skF_3',D_276,'#skF_7'),F_274) = k1_funct_1('#skF_7',k1_funct_1(D_276,F_274))
      | k1_xboole_0 = B_275
      | ~ r1_tarski(k2_relset_1(B_275,'#skF_5',D_276),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_274,B_275)
      | ~ m1_subset_1(D_276,k1_zfmisc_1(k2_zfmisc_1(B_275,'#skF_5')))
      | ~ v1_funct_2(D_276,B_275,'#skF_5')
      | ~ v1_funct_1(D_276)
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_1483])).

tff(c_1667,plain,(
    ! [B_289,D_290,F_291] :
      ( k1_funct_1(k8_funct_2(B_289,'#skF_5','#skF_3',D_290,'#skF_7'),F_291) = k1_funct_1('#skF_7',k1_funct_1(D_290,F_291))
      | k1_xboole_0 = B_289
      | ~ r1_tarski(k2_relset_1(B_289,'#skF_5',D_290),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_291,B_289)
      | ~ m1_subset_1(D_290,k1_zfmisc_1(k2_zfmisc_1(B_289,'#skF_5')))
      | ~ v1_funct_2(D_290,B_289,'#skF_5')
      | ~ v1_funct_1(D_290) ) ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_1495])).

tff(c_1672,plain,(
    ! [F_291] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_291) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_291))
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_291,'#skF_4')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_389,c_1667])).

tff(c_1676,plain,(
    ! [F_291] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_291) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_291))
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1(F_291,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_98,c_480,c_1672])).

tff(c_1677,plain,(
    ! [F_291] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_291) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_291))
      | ~ m1_subset_1(F_291,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_1676])).

tff(c_335,plain,(
    ! [C_131,B_132,A_133] :
      ( v5_relat_1(C_131,B_132)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_133,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_353,plain,(
    v5_relat_1('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_335])).

tff(c_185,plain,(
    ! [C_106,A_107,B_108] :
      ( v1_relat_1(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_201,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_94,c_185])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_135,plain,(
    ! [A_97] :
      ( v1_xboole_0(A_97)
      | r2_hidden('#skF_1'(A_97),A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    ! [B_26,A_25] :
      ( ~ r1_tarski(B_26,A_25)
      | ~ r2_hidden(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_144,plain,(
    ! [A_98] :
      ( ~ r1_tarski(A_98,'#skF_1'(A_98))
      | v1_xboole_0(A_98) ) ),
    inference(resolution,[status(thm)],[c_135,c_38])).

tff(c_149,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_144])).

tff(c_16,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1238,plain,(
    ! [B_259,D_260,A_261,C_262] :
      ( k1_xboole_0 = B_259
      | v1_funct_2(D_260,A_261,C_262)
      | ~ r1_tarski(k2_relset_1(A_261,B_259,D_260),C_262)
      | ~ m1_subset_1(D_260,k1_zfmisc_1(k2_zfmisc_1(A_261,B_259)))
      | ~ v1_funct_2(D_260,A_261,B_259)
      | ~ v1_funct_1(D_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_1248,plain,(
    ! [C_262] :
      ( k1_xboole_0 = '#skF_5'
      | v1_funct_2('#skF_6','#skF_4',C_262)
      | ~ r1_tarski(k2_relat_1('#skF_6'),C_262)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_389,c_1238])).

tff(c_1256,plain,(
    ! [C_262] :
      ( k1_xboole_0 = '#skF_5'
      | v1_funct_2('#skF_6','#skF_4',C_262)
      | ~ r1_tarski(k2_relat_1('#skF_6'),C_262) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_98,c_1248])).

tff(c_1259,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1256])).

tff(c_1296,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1259,c_149])).

tff(c_1304,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_1296])).

tff(c_1306,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1256])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( r2_hidden(A_15,B_16)
      | v1_xboole_0(B_16)
      | ~ m1_subset_1(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1129,plain,(
    ! [D_242,C_243,B_244,A_245] :
      ( r2_hidden(k1_funct_1(D_242,C_243),B_244)
      | k1_xboole_0 = B_244
      | ~ r2_hidden(C_243,A_245)
      | ~ m1_subset_1(D_242,k1_zfmisc_1(k2_zfmisc_1(A_245,B_244)))
      | ~ v1_funct_2(D_242,A_245,B_244)
      | ~ v1_funct_1(D_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_3271,plain,(
    ! [D_418,A_419,B_420,B_421] :
      ( r2_hidden(k1_funct_1(D_418,A_419),B_420)
      | k1_xboole_0 = B_420
      | ~ m1_subset_1(D_418,k1_zfmisc_1(k2_zfmisc_1(B_421,B_420)))
      | ~ v1_funct_2(D_418,B_421,B_420)
      | ~ v1_funct_1(D_418)
      | v1_xboole_0(B_421)
      | ~ m1_subset_1(A_419,B_421) ) ),
    inference(resolution,[status(thm)],[c_22,c_1129])).

tff(c_3294,plain,(
    ! [A_419] :
      ( r2_hidden(k1_funct_1('#skF_6',A_419),'#skF_5')
      | k1_xboole_0 = '#skF_5'
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_419,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_98,c_3271])).

tff(c_3315,plain,(
    ! [A_419] :
      ( r2_hidden(k1_funct_1('#skF_6',A_419),'#skF_5')
      | k1_xboole_0 = '#skF_5'
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_419,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_3294])).

tff(c_3316,plain,(
    ! [A_419] :
      ( r2_hidden(k1_funct_1('#skF_6',A_419),'#skF_5')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_419,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1306,c_3315])).

tff(c_3317,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3316])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3331,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3317,c_6])).

tff(c_3343,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_3331])).

tff(c_3345,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_3316])).

tff(c_1307,plain,(
    ! [C_263] :
      ( v1_funct_2('#skF_6','#skF_4',C_263)
      | ~ r1_tarski(k2_relat_1('#skF_6'),C_263) ) ),
    inference(splitRight,[status(thm)],[c_1256])).

tff(c_1321,plain,(
    v1_funct_2('#skF_6','#skF_4',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_480,c_1307])).

tff(c_1322,plain,(
    ! [B_264,D_265,A_266,C_267] :
      ( k1_xboole_0 = B_264
      | m1_subset_1(D_265,k1_zfmisc_1(k2_zfmisc_1(A_266,C_267)))
      | ~ r1_tarski(k2_relset_1(A_266,B_264,D_265),C_267)
      | ~ m1_subset_1(D_265,k1_zfmisc_1(k2_zfmisc_1(A_266,B_264)))
      | ~ v1_funct_2(D_265,A_266,B_264)
      | ~ v1_funct_1(D_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_1332,plain,(
    ! [C_267] :
      ( k1_xboole_0 = '#skF_5'
      | m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',C_267)))
      | ~ r1_tarski(k2_relat_1('#skF_6'),C_267)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_389,c_1322])).

tff(c_1341,plain,(
    ! [C_267] :
      ( k1_xboole_0 = '#skF_5'
      | m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',C_267)))
      | ~ r1_tarski(k2_relat_1('#skF_6'),C_267) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_98,c_1332])).

tff(c_1342,plain,(
    ! [C_267] :
      ( m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',C_267)))
      | ~ r1_tarski(k2_relat_1('#skF_6'),C_267) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1306,c_1341])).

tff(c_26,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_247,plain,(
    ! [B_116,A_117] :
      ( v1_xboole_0(B_116)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(A_117))
      | ~ v1_xboole_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_262,plain,(
    ! [A_118,B_119] :
      ( v1_xboole_0(A_118)
      | ~ v1_xboole_0(B_119)
      | ~ r1_tarski(A_118,B_119) ) ),
    inference(resolution,[status(thm)],[c_26,c_247])).

tff(c_277,plain,
    ( v1_xboole_0(k2_relset_1('#skF_4','#skF_5','#skF_6'))
    | ~ v1_xboole_0(k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(resolution,[status(thm)],[c_90,c_262])).

tff(c_332,plain,(
    ~ v1_xboole_0(k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_277])).

tff(c_481,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_332])).

tff(c_1345,plain,(
    ! [C_268] :
      ( m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',C_268)))
      | ~ r1_tarski(k2_relat_1('#skF_6'),C_268) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1306,c_1341])).

tff(c_24,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ m1_subset_1(A_17,k1_zfmisc_1(B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1425,plain,(
    ! [C_271] :
      ( r1_tarski('#skF_6',k2_zfmisc_1('#skF_4',C_271))
      | ~ r1_tarski(k2_relat_1('#skF_6'),C_271) ) ),
    inference(resolution,[status(thm)],[c_1345,c_24])).

tff(c_1440,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_4',k1_relat_1('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_480,c_1425])).

tff(c_387,plain,(
    ! [A_140,B_141,A_17] :
      ( k2_relset_1(A_140,B_141,A_17) = k2_relat_1(A_17)
      | ~ r1_tarski(A_17,k2_zfmisc_1(A_140,B_141)) ) ),
    inference(resolution,[status(thm)],[c_26,c_370])).

tff(c_1462,plain,(
    k2_relset_1('#skF_4',k1_relat_1('#skF_7'),'#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1440,c_387])).

tff(c_58,plain,(
    ! [E_61,A_47,F_63,D_57,C_49,B_48] :
      ( k1_funct_1(k8_funct_2(B_48,C_49,A_47,D_57,E_61),F_63) = k1_funct_1(E_61,k1_funct_1(D_57,F_63))
      | k1_xboole_0 = B_48
      | ~ r1_tarski(k2_relset_1(B_48,C_49,D_57),k1_relset_1(C_49,A_47,E_61))
      | ~ m1_subset_1(F_63,B_48)
      | ~ m1_subset_1(E_61,k1_zfmisc_1(k2_zfmisc_1(C_49,A_47)))
      | ~ v1_funct_1(E_61)
      | ~ m1_subset_1(D_57,k1_zfmisc_1(k2_zfmisc_1(B_48,C_49)))
      | ~ v1_funct_2(D_57,B_48,C_49)
      | ~ v1_funct_1(D_57)
      | v1_xboole_0(C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_1513,plain,(
    ! [A_47,E_61,F_63] :
      ( k1_funct_1(k8_funct_2('#skF_4',k1_relat_1('#skF_7'),A_47,'#skF_6',E_61),F_63) = k1_funct_1(E_61,k1_funct_1('#skF_6',F_63))
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relset_1(k1_relat_1('#skF_7'),A_47,E_61))
      | ~ m1_subset_1(F_63,'#skF_4')
      | ~ m1_subset_1(E_61,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_7'),A_47)))
      | ~ v1_funct_1(E_61)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_7'))))
      | ~ v1_funct_2('#skF_6','#skF_4',k1_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0(k1_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1462,c_58])).

tff(c_1521,plain,(
    ! [A_47,E_61,F_63] :
      ( k1_funct_1(k8_funct_2('#skF_4',k1_relat_1('#skF_7'),A_47,'#skF_6',E_61),F_63) = k1_funct_1(E_61,k1_funct_1('#skF_6',F_63))
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relset_1(k1_relat_1('#skF_7'),A_47,E_61))
      | ~ m1_subset_1(F_63,'#skF_4')
      | ~ m1_subset_1(E_61,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_7'),A_47)))
      | ~ v1_funct_1(E_61)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_7'))))
      | v1_xboole_0(k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_1321,c_1513])).

tff(c_1522,plain,(
    ! [A_47,E_61,F_63] :
      ( k1_funct_1(k8_funct_2('#skF_4',k1_relat_1('#skF_7'),A_47,'#skF_6',E_61),F_63) = k1_funct_1(E_61,k1_funct_1('#skF_6',F_63))
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relset_1(k1_relat_1('#skF_7'),A_47,E_61))
      | ~ m1_subset_1(F_63,'#skF_4')
      | ~ m1_subset_1(E_61,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_7'),A_47)))
      | ~ v1_funct_1(E_61)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_7')))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_481,c_88,c_1521])).

tff(c_2010,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_7')))) ),
    inference(splitLeft,[status(thm)],[c_1522])).

tff(c_2013,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_1342,c_2010])).

tff(c_2020,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_2013])).

tff(c_2022,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_7')))) ),
    inference(splitRight,[status(thm)],[c_1522])).

tff(c_3277,plain,(
    ! [A_419] :
      ( r2_hidden(k1_funct_1('#skF_6',A_419),k1_relat_1('#skF_7'))
      | k1_relat_1('#skF_7') = k1_xboole_0
      | ~ v1_funct_2('#skF_6','#skF_4',k1_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_419,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2022,c_3271])).

tff(c_3299,plain,(
    ! [A_419] :
      ( r2_hidden(k1_funct_1('#skF_6',A_419),k1_relat_1('#skF_7'))
      | k1_relat_1('#skF_7') = k1_xboole_0
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_419,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_1321,c_3277])).

tff(c_3398,plain,(
    ! [A_419] :
      ( r2_hidden(k1_funct_1('#skF_6',A_419),k1_relat_1('#skF_7'))
      | k1_relat_1('#skF_7') = k1_xboole_0
      | ~ m1_subset_1(A_419,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_3345,c_3299])).

tff(c_3399,plain,(
    k1_relat_1('#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3398])).

tff(c_813,plain,(
    ! [C_208,A_209,B_210] :
      ( ~ v1_xboole_0(C_208)
      | ~ v1_funct_2(C_208,A_209,B_210)
      | ~ v1_funct_1(C_208)
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(A_209,B_210)))
      | v1_xboole_0(B_210)
      | v1_xboole_0(A_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_829,plain,
    ( ~ v1_xboole_0('#skF_6')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_98,c_813])).

tff(c_839,plain,
    ( ~ v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_829])).

tff(c_840,plain,
    ( ~ v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_839])).

tff(c_841,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_840])).

tff(c_20,plain,(
    ! [B_14,A_12] :
      ( v1_xboole_0(B_14)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_12))
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1363,plain,(
    ! [C_268] :
      ( v1_xboole_0('#skF_6')
      | ~ v1_xboole_0(k2_zfmisc_1('#skF_4',C_268))
      | ~ r1_tarski(k2_relat_1('#skF_6'),C_268) ) ),
    inference(resolution,[status(thm)],[c_1345,c_20])).

tff(c_1403,plain,(
    ! [C_270] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_4',C_270))
      | ~ r1_tarski(k2_relat_1('#skF_6'),C_270) ) ),
    inference(negUnitSimplification,[status(thm)],[c_841,c_1363])).

tff(c_1419,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_480,c_1403])).

tff(c_3410,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3399,c_1419])).

tff(c_3423,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_16,c_3410])).

tff(c_3691,plain,(
    ! [A_434] :
      ( r2_hidden(k1_funct_1('#skF_6',A_434),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(A_434,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_3398])).

tff(c_56,plain,(
    ! [A_43,B_44,C_46] :
      ( k7_partfun1(A_43,B_44,C_46) = k1_funct_1(B_44,C_46)
      | ~ r2_hidden(C_46,k1_relat_1(B_44))
      | ~ v1_funct_1(B_44)
      | ~ v5_relat_1(B_44,A_43)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_3703,plain,(
    ! [A_43,A_434] :
      ( k7_partfun1(A_43,'#skF_7',k1_funct_1('#skF_6',A_434)) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',A_434))
      | ~ v1_funct_1('#skF_7')
      | ~ v5_relat_1('#skF_7',A_43)
      | ~ v1_relat_1('#skF_7')
      | ~ m1_subset_1(A_434,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3691,c_56])).

tff(c_3788,plain,(
    ! [A_441,A_442] :
      ( k7_partfun1(A_441,'#skF_7',k1_funct_1('#skF_6',A_442)) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',A_442))
      | ~ v5_relat_1('#skF_7',A_441)
      | ~ m1_subset_1(A_442,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_96,c_3703])).

tff(c_86,plain,(
    k7_partfun1('#skF_3','#skF_7',k1_funct_1('#skF_6','#skF_8')) != k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_3794,plain,
    ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
    | ~ v5_relat_1('#skF_7','#skF_3')
    | ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3788,c_86])).

tff(c_3800,plain,(
    k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_353,c_3794])).

tff(c_3804,plain,(
    ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1677,c_3800])).

tff(c_3808,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_3804])).

tff(c_3809,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_840])).

tff(c_3816,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3809,c_6])).

tff(c_3824,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_3816])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:22:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.49/2.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.49/2.49  
% 7.49/2.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.49/2.49  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_8 > #skF_4
% 7.49/2.49  
% 7.49/2.49  %Foreground sorts:
% 7.49/2.49  
% 7.49/2.49  
% 7.49/2.49  %Background operators:
% 7.49/2.49  
% 7.49/2.49  
% 7.49/2.49  %Foreground operators:
% 7.49/2.49  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.49/2.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.49/2.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.49/2.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.49/2.49  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.49/2.49  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.49/2.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.49/2.49  tff('#skF_7', type, '#skF_7': $i).
% 7.49/2.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.49/2.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.49/2.49  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 7.49/2.49  tff('#skF_5', type, '#skF_5': $i).
% 7.49/2.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.49/2.49  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 7.49/2.49  tff('#skF_6', type, '#skF_6': $i).
% 7.49/2.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.49/2.49  tff('#skF_3', type, '#skF_3': $i).
% 7.49/2.49  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.49/2.49  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.49/2.49  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.49/2.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.49/2.49  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.49/2.49  tff('#skF_8', type, '#skF_8': $i).
% 7.49/2.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.49/2.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.49/2.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.49/2.49  tff('#skF_4', type, '#skF_4': $i).
% 7.49/2.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.49/2.49  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.49/2.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.49/2.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.49/2.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.49/2.49  
% 7.77/2.51  tff(f_243, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t186_funct_2)).
% 7.77/2.51  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.77/2.51  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.77/2.51  tff(f_170, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 7.77/2.51  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.77/2.51  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.77/2.51  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.77/2.51  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.77/2.51  tff(f_97, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 7.77/2.51  tff(f_53, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.77/2.51  tff(f_218, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_2)).
% 7.77/2.51  tff(f_66, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 7.77/2.51  tff(f_199, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 7.77/2.51  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 7.77/2.51  tff(f_70, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.77/2.51  tff(f_60, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 7.77/2.51  tff(f_135, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => ((v1_funct_1(C) & ~v1_xboole_0(C)) & v1_funct_2(C, A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_funct_2)).
% 7.77/2.51  tff(f_146, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 7.77/2.51  tff(c_88, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_243])).
% 7.77/2.51  tff(c_92, plain, (m1_subset_1('#skF_8', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_243])).
% 7.77/2.51  tff(c_102, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_243])).
% 7.77/2.51  tff(c_100, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_243])).
% 7.77/2.51  tff(c_98, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_243])).
% 7.77/2.51  tff(c_94, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_243])).
% 7.77/2.51  tff(c_459, plain, (![A_153, B_154, C_155]: (k1_relset_1(A_153, B_154, C_155)=k1_relat_1(C_155) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.77/2.51  tff(c_477, plain, (k1_relset_1('#skF_5', '#skF_3', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_94, c_459])).
% 7.77/2.51  tff(c_370, plain, (![A_140, B_141, C_142]: (k2_relset_1(A_140, B_141, C_142)=k2_relat_1(C_142) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.77/2.51  tff(c_389, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_98, c_370])).
% 7.77/2.51  tff(c_90, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_243])).
% 7.77/2.51  tff(c_394, plain, (r1_tarski(k2_relat_1('#skF_6'), k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_389, c_90])).
% 7.77/2.51  tff(c_480, plain, (r1_tarski(k2_relat_1('#skF_6'), k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_477, c_394])).
% 7.77/2.51  tff(c_104, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_243])).
% 7.77/2.51  tff(c_96, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_243])).
% 7.77/2.51  tff(c_1475, plain, (![C_277, A_272, B_275, F_274, E_273, D_276]: (k1_funct_1(k8_funct_2(B_275, C_277, A_272, D_276, E_273), F_274)=k1_funct_1(E_273, k1_funct_1(D_276, F_274)) | k1_xboole_0=B_275 | ~r1_tarski(k2_relset_1(B_275, C_277, D_276), k1_relset_1(C_277, A_272, E_273)) | ~m1_subset_1(F_274, B_275) | ~m1_subset_1(E_273, k1_zfmisc_1(k2_zfmisc_1(C_277, A_272))) | ~v1_funct_1(E_273) | ~m1_subset_1(D_276, k1_zfmisc_1(k2_zfmisc_1(B_275, C_277))) | ~v1_funct_2(D_276, B_275, C_277) | ~v1_funct_1(D_276) | v1_xboole_0(C_277))), inference(cnfTransformation, [status(thm)], [f_170])).
% 7.77/2.51  tff(c_1483, plain, (![B_275, D_276, F_274]: (k1_funct_1(k8_funct_2(B_275, '#skF_5', '#skF_3', D_276, '#skF_7'), F_274)=k1_funct_1('#skF_7', k1_funct_1(D_276, F_274)) | k1_xboole_0=B_275 | ~r1_tarski(k2_relset_1(B_275, '#skF_5', D_276), k1_relat_1('#skF_7')) | ~m1_subset_1(F_274, B_275) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3'))) | ~v1_funct_1('#skF_7') | ~m1_subset_1(D_276, k1_zfmisc_1(k2_zfmisc_1(B_275, '#skF_5'))) | ~v1_funct_2(D_276, B_275, '#skF_5') | ~v1_funct_1(D_276) | v1_xboole_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_477, c_1475])).
% 7.77/2.51  tff(c_1495, plain, (![B_275, D_276, F_274]: (k1_funct_1(k8_funct_2(B_275, '#skF_5', '#skF_3', D_276, '#skF_7'), F_274)=k1_funct_1('#skF_7', k1_funct_1(D_276, F_274)) | k1_xboole_0=B_275 | ~r1_tarski(k2_relset_1(B_275, '#skF_5', D_276), k1_relat_1('#skF_7')) | ~m1_subset_1(F_274, B_275) | ~m1_subset_1(D_276, k1_zfmisc_1(k2_zfmisc_1(B_275, '#skF_5'))) | ~v1_funct_2(D_276, B_275, '#skF_5') | ~v1_funct_1(D_276) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_1483])).
% 7.77/2.51  tff(c_1667, plain, (![B_289, D_290, F_291]: (k1_funct_1(k8_funct_2(B_289, '#skF_5', '#skF_3', D_290, '#skF_7'), F_291)=k1_funct_1('#skF_7', k1_funct_1(D_290, F_291)) | k1_xboole_0=B_289 | ~r1_tarski(k2_relset_1(B_289, '#skF_5', D_290), k1_relat_1('#skF_7')) | ~m1_subset_1(F_291, B_289) | ~m1_subset_1(D_290, k1_zfmisc_1(k2_zfmisc_1(B_289, '#skF_5'))) | ~v1_funct_2(D_290, B_289, '#skF_5') | ~v1_funct_1(D_290))), inference(negUnitSimplification, [status(thm)], [c_104, c_1495])).
% 7.77/2.51  tff(c_1672, plain, (![F_291]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_291)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_291)) | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relat_1('#skF_6'), k1_relat_1('#skF_7')) | ~m1_subset_1(F_291, '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_389, c_1667])).
% 7.77/2.51  tff(c_1676, plain, (![F_291]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_291)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_291)) | k1_xboole_0='#skF_4' | ~m1_subset_1(F_291, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_98, c_480, c_1672])).
% 7.77/2.51  tff(c_1677, plain, (![F_291]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_291)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_291)) | ~m1_subset_1(F_291, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_88, c_1676])).
% 7.77/2.51  tff(c_335, plain, (![C_131, B_132, A_133]: (v5_relat_1(C_131, B_132) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_133, B_132))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.77/2.51  tff(c_353, plain, (v5_relat_1('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_94, c_335])).
% 7.77/2.51  tff(c_185, plain, (![C_106, A_107, B_108]: (v1_relat_1(C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.77/2.51  tff(c_201, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_94, c_185])).
% 7.77/2.51  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.77/2.51  tff(c_135, plain, (![A_97]: (v1_xboole_0(A_97) | r2_hidden('#skF_1'(A_97), A_97))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.77/2.51  tff(c_38, plain, (![B_26, A_25]: (~r1_tarski(B_26, A_25) | ~r2_hidden(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.77/2.51  tff(c_144, plain, (![A_98]: (~r1_tarski(A_98, '#skF_1'(A_98)) | v1_xboole_0(A_98))), inference(resolution, [status(thm)], [c_135, c_38])).
% 7.77/2.51  tff(c_149, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_144])).
% 7.77/2.51  tff(c_16, plain, (![A_10]: (k2_zfmisc_1(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.77/2.51  tff(c_1238, plain, (![B_259, D_260, A_261, C_262]: (k1_xboole_0=B_259 | v1_funct_2(D_260, A_261, C_262) | ~r1_tarski(k2_relset_1(A_261, B_259, D_260), C_262) | ~m1_subset_1(D_260, k1_zfmisc_1(k2_zfmisc_1(A_261, B_259))) | ~v1_funct_2(D_260, A_261, B_259) | ~v1_funct_1(D_260))), inference(cnfTransformation, [status(thm)], [f_218])).
% 7.77/2.51  tff(c_1248, plain, (![C_262]: (k1_xboole_0='#skF_5' | v1_funct_2('#skF_6', '#skF_4', C_262) | ~r1_tarski(k2_relat_1('#skF_6'), C_262) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_389, c_1238])).
% 7.77/2.51  tff(c_1256, plain, (![C_262]: (k1_xboole_0='#skF_5' | v1_funct_2('#skF_6', '#skF_4', C_262) | ~r1_tarski(k2_relat_1('#skF_6'), C_262))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_98, c_1248])).
% 7.77/2.51  tff(c_1259, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_1256])).
% 7.77/2.51  tff(c_1296, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1259, c_149])).
% 7.77/2.51  tff(c_1304, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_1296])).
% 7.77/2.51  tff(c_1306, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_1256])).
% 7.77/2.51  tff(c_22, plain, (![A_15, B_16]: (r2_hidden(A_15, B_16) | v1_xboole_0(B_16) | ~m1_subset_1(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.77/2.51  tff(c_1129, plain, (![D_242, C_243, B_244, A_245]: (r2_hidden(k1_funct_1(D_242, C_243), B_244) | k1_xboole_0=B_244 | ~r2_hidden(C_243, A_245) | ~m1_subset_1(D_242, k1_zfmisc_1(k2_zfmisc_1(A_245, B_244))) | ~v1_funct_2(D_242, A_245, B_244) | ~v1_funct_1(D_242))), inference(cnfTransformation, [status(thm)], [f_199])).
% 7.77/2.51  tff(c_3271, plain, (![D_418, A_419, B_420, B_421]: (r2_hidden(k1_funct_1(D_418, A_419), B_420) | k1_xboole_0=B_420 | ~m1_subset_1(D_418, k1_zfmisc_1(k2_zfmisc_1(B_421, B_420))) | ~v1_funct_2(D_418, B_421, B_420) | ~v1_funct_1(D_418) | v1_xboole_0(B_421) | ~m1_subset_1(A_419, B_421))), inference(resolution, [status(thm)], [c_22, c_1129])).
% 7.77/2.51  tff(c_3294, plain, (![A_419]: (r2_hidden(k1_funct_1('#skF_6', A_419), '#skF_5') | k1_xboole_0='#skF_5' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_4') | ~m1_subset_1(A_419, '#skF_4'))), inference(resolution, [status(thm)], [c_98, c_3271])).
% 7.77/2.51  tff(c_3315, plain, (![A_419]: (r2_hidden(k1_funct_1('#skF_6', A_419), '#skF_5') | k1_xboole_0='#skF_5' | v1_xboole_0('#skF_4') | ~m1_subset_1(A_419, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_3294])).
% 7.77/2.51  tff(c_3316, plain, (![A_419]: (r2_hidden(k1_funct_1('#skF_6', A_419), '#skF_5') | v1_xboole_0('#skF_4') | ~m1_subset_1(A_419, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1306, c_3315])).
% 7.77/2.51  tff(c_3317, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_3316])).
% 7.77/2.51  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.77/2.51  tff(c_3331, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_3317, c_6])).
% 7.77/2.51  tff(c_3343, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_3331])).
% 7.77/2.51  tff(c_3345, plain, (~v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_3316])).
% 7.77/2.51  tff(c_1307, plain, (![C_263]: (v1_funct_2('#skF_6', '#skF_4', C_263) | ~r1_tarski(k2_relat_1('#skF_6'), C_263))), inference(splitRight, [status(thm)], [c_1256])).
% 7.77/2.51  tff(c_1321, plain, (v1_funct_2('#skF_6', '#skF_4', k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_480, c_1307])).
% 7.77/2.51  tff(c_1322, plain, (![B_264, D_265, A_266, C_267]: (k1_xboole_0=B_264 | m1_subset_1(D_265, k1_zfmisc_1(k2_zfmisc_1(A_266, C_267))) | ~r1_tarski(k2_relset_1(A_266, B_264, D_265), C_267) | ~m1_subset_1(D_265, k1_zfmisc_1(k2_zfmisc_1(A_266, B_264))) | ~v1_funct_2(D_265, A_266, B_264) | ~v1_funct_1(D_265))), inference(cnfTransformation, [status(thm)], [f_218])).
% 7.77/2.51  tff(c_1332, plain, (![C_267]: (k1_xboole_0='#skF_5' | m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', C_267))) | ~r1_tarski(k2_relat_1('#skF_6'), C_267) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_389, c_1322])).
% 7.77/2.51  tff(c_1341, plain, (![C_267]: (k1_xboole_0='#skF_5' | m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', C_267))) | ~r1_tarski(k2_relat_1('#skF_6'), C_267))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_98, c_1332])).
% 7.77/2.51  tff(c_1342, plain, (![C_267]: (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', C_267))) | ~r1_tarski(k2_relat_1('#skF_6'), C_267))), inference(negUnitSimplification, [status(thm)], [c_1306, c_1341])).
% 7.77/2.51  tff(c_26, plain, (![A_17, B_18]: (m1_subset_1(A_17, k1_zfmisc_1(B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.77/2.51  tff(c_247, plain, (![B_116, A_117]: (v1_xboole_0(B_116) | ~m1_subset_1(B_116, k1_zfmisc_1(A_117)) | ~v1_xboole_0(A_117))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.77/2.51  tff(c_262, plain, (![A_118, B_119]: (v1_xboole_0(A_118) | ~v1_xboole_0(B_119) | ~r1_tarski(A_118, B_119))), inference(resolution, [status(thm)], [c_26, c_247])).
% 7.77/2.51  tff(c_277, plain, (v1_xboole_0(k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | ~v1_xboole_0(k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(resolution, [status(thm)], [c_90, c_262])).
% 7.77/2.51  tff(c_332, plain, (~v1_xboole_0(k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(splitLeft, [status(thm)], [c_277])).
% 7.77/2.51  tff(c_481, plain, (~v1_xboole_0(k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_477, c_332])).
% 7.77/2.51  tff(c_1345, plain, (![C_268]: (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', C_268))) | ~r1_tarski(k2_relat_1('#skF_6'), C_268))), inference(negUnitSimplification, [status(thm)], [c_1306, c_1341])).
% 7.77/2.51  tff(c_24, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~m1_subset_1(A_17, k1_zfmisc_1(B_18)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.77/2.51  tff(c_1425, plain, (![C_271]: (r1_tarski('#skF_6', k2_zfmisc_1('#skF_4', C_271)) | ~r1_tarski(k2_relat_1('#skF_6'), C_271))), inference(resolution, [status(thm)], [c_1345, c_24])).
% 7.77/2.51  tff(c_1440, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_4', k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_480, c_1425])).
% 7.77/2.51  tff(c_387, plain, (![A_140, B_141, A_17]: (k2_relset_1(A_140, B_141, A_17)=k2_relat_1(A_17) | ~r1_tarski(A_17, k2_zfmisc_1(A_140, B_141)))), inference(resolution, [status(thm)], [c_26, c_370])).
% 7.77/2.51  tff(c_1462, plain, (k2_relset_1('#skF_4', k1_relat_1('#skF_7'), '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1440, c_387])).
% 7.77/2.51  tff(c_58, plain, (![E_61, A_47, F_63, D_57, C_49, B_48]: (k1_funct_1(k8_funct_2(B_48, C_49, A_47, D_57, E_61), F_63)=k1_funct_1(E_61, k1_funct_1(D_57, F_63)) | k1_xboole_0=B_48 | ~r1_tarski(k2_relset_1(B_48, C_49, D_57), k1_relset_1(C_49, A_47, E_61)) | ~m1_subset_1(F_63, B_48) | ~m1_subset_1(E_61, k1_zfmisc_1(k2_zfmisc_1(C_49, A_47))) | ~v1_funct_1(E_61) | ~m1_subset_1(D_57, k1_zfmisc_1(k2_zfmisc_1(B_48, C_49))) | ~v1_funct_2(D_57, B_48, C_49) | ~v1_funct_1(D_57) | v1_xboole_0(C_49))), inference(cnfTransformation, [status(thm)], [f_170])).
% 7.77/2.51  tff(c_1513, plain, (![A_47, E_61, F_63]: (k1_funct_1(k8_funct_2('#skF_4', k1_relat_1('#skF_7'), A_47, '#skF_6', E_61), F_63)=k1_funct_1(E_61, k1_funct_1('#skF_6', F_63)) | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relat_1('#skF_6'), k1_relset_1(k1_relat_1('#skF_7'), A_47, E_61)) | ~m1_subset_1(F_63, '#skF_4') | ~m1_subset_1(E_61, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_7'), A_47))) | ~v1_funct_1(E_61) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_7')))) | ~v1_funct_2('#skF_6', '#skF_4', k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_6') | v1_xboole_0(k1_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_1462, c_58])).
% 7.77/2.51  tff(c_1521, plain, (![A_47, E_61, F_63]: (k1_funct_1(k8_funct_2('#skF_4', k1_relat_1('#skF_7'), A_47, '#skF_6', E_61), F_63)=k1_funct_1(E_61, k1_funct_1('#skF_6', F_63)) | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relat_1('#skF_6'), k1_relset_1(k1_relat_1('#skF_7'), A_47, E_61)) | ~m1_subset_1(F_63, '#skF_4') | ~m1_subset_1(E_61, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_7'), A_47))) | ~v1_funct_1(E_61) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_7')))) | v1_xboole_0(k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_1321, c_1513])).
% 7.77/2.51  tff(c_1522, plain, (![A_47, E_61, F_63]: (k1_funct_1(k8_funct_2('#skF_4', k1_relat_1('#skF_7'), A_47, '#skF_6', E_61), F_63)=k1_funct_1(E_61, k1_funct_1('#skF_6', F_63)) | ~r1_tarski(k2_relat_1('#skF_6'), k1_relset_1(k1_relat_1('#skF_7'), A_47, E_61)) | ~m1_subset_1(F_63, '#skF_4') | ~m1_subset_1(E_61, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_7'), A_47))) | ~v1_funct_1(E_61) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_7')))))), inference(negUnitSimplification, [status(thm)], [c_481, c_88, c_1521])).
% 7.77/2.51  tff(c_2010, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_7'))))), inference(splitLeft, [status(thm)], [c_1522])).
% 7.77/2.51  tff(c_2013, plain, (~r1_tarski(k2_relat_1('#skF_6'), k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_1342, c_2010])).
% 7.77/2.51  tff(c_2020, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_480, c_2013])).
% 7.77/2.51  tff(c_2022, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_7'))))), inference(splitRight, [status(thm)], [c_1522])).
% 7.77/2.51  tff(c_3277, plain, (![A_419]: (r2_hidden(k1_funct_1('#skF_6', A_419), k1_relat_1('#skF_7')) | k1_relat_1('#skF_7')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_4', k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_4') | ~m1_subset_1(A_419, '#skF_4'))), inference(resolution, [status(thm)], [c_2022, c_3271])).
% 7.77/2.51  tff(c_3299, plain, (![A_419]: (r2_hidden(k1_funct_1('#skF_6', A_419), k1_relat_1('#skF_7')) | k1_relat_1('#skF_7')=k1_xboole_0 | v1_xboole_0('#skF_4') | ~m1_subset_1(A_419, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_1321, c_3277])).
% 7.77/2.51  tff(c_3398, plain, (![A_419]: (r2_hidden(k1_funct_1('#skF_6', A_419), k1_relat_1('#skF_7')) | k1_relat_1('#skF_7')=k1_xboole_0 | ~m1_subset_1(A_419, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_3345, c_3299])).
% 7.77/2.51  tff(c_3399, plain, (k1_relat_1('#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3398])).
% 7.77/2.51  tff(c_813, plain, (![C_208, A_209, B_210]: (~v1_xboole_0(C_208) | ~v1_funct_2(C_208, A_209, B_210) | ~v1_funct_1(C_208) | ~m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(A_209, B_210))) | v1_xboole_0(B_210) | v1_xboole_0(A_209))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.77/2.51  tff(c_829, plain, (~v1_xboole_0('#skF_6') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_98, c_813])).
% 7.77/2.51  tff(c_839, plain, (~v1_xboole_0('#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_829])).
% 7.77/2.51  tff(c_840, plain, (~v1_xboole_0('#skF_6') | v1_xboole_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_104, c_839])).
% 7.77/2.51  tff(c_841, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_840])).
% 7.77/2.51  tff(c_20, plain, (![B_14, A_12]: (v1_xboole_0(B_14) | ~m1_subset_1(B_14, k1_zfmisc_1(A_12)) | ~v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.77/2.51  tff(c_1363, plain, (![C_268]: (v1_xboole_0('#skF_6') | ~v1_xboole_0(k2_zfmisc_1('#skF_4', C_268)) | ~r1_tarski(k2_relat_1('#skF_6'), C_268))), inference(resolution, [status(thm)], [c_1345, c_20])).
% 7.77/2.51  tff(c_1403, plain, (![C_270]: (~v1_xboole_0(k2_zfmisc_1('#skF_4', C_270)) | ~r1_tarski(k2_relat_1('#skF_6'), C_270))), inference(negUnitSimplification, [status(thm)], [c_841, c_1363])).
% 7.77/2.51  tff(c_1419, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_480, c_1403])).
% 7.77/2.51  tff(c_3410, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_3399, c_1419])).
% 7.77/2.51  tff(c_3423, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_149, c_16, c_3410])).
% 7.77/2.51  tff(c_3691, plain, (![A_434]: (r2_hidden(k1_funct_1('#skF_6', A_434), k1_relat_1('#skF_7')) | ~m1_subset_1(A_434, '#skF_4'))), inference(splitRight, [status(thm)], [c_3398])).
% 7.77/2.51  tff(c_56, plain, (![A_43, B_44, C_46]: (k7_partfun1(A_43, B_44, C_46)=k1_funct_1(B_44, C_46) | ~r2_hidden(C_46, k1_relat_1(B_44)) | ~v1_funct_1(B_44) | ~v5_relat_1(B_44, A_43) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.77/2.51  tff(c_3703, plain, (![A_43, A_434]: (k7_partfun1(A_43, '#skF_7', k1_funct_1('#skF_6', A_434))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', A_434)) | ~v1_funct_1('#skF_7') | ~v5_relat_1('#skF_7', A_43) | ~v1_relat_1('#skF_7') | ~m1_subset_1(A_434, '#skF_4'))), inference(resolution, [status(thm)], [c_3691, c_56])).
% 7.77/2.51  tff(c_3788, plain, (![A_441, A_442]: (k7_partfun1(A_441, '#skF_7', k1_funct_1('#skF_6', A_442))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', A_442)) | ~v5_relat_1('#skF_7', A_441) | ~m1_subset_1(A_442, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_201, c_96, c_3703])).
% 7.77/2.51  tff(c_86, plain, (k7_partfun1('#skF_3', '#skF_7', k1_funct_1('#skF_6', '#skF_8'))!=k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_243])).
% 7.77/2.51  tff(c_3794, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | ~v5_relat_1('#skF_7', '#skF_3') | ~m1_subset_1('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3788, c_86])).
% 7.77/2.51  tff(c_3800, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_353, c_3794])).
% 7.77/2.51  tff(c_3804, plain, (~m1_subset_1('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1677, c_3800])).
% 7.77/2.51  tff(c_3808, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_3804])).
% 7.77/2.51  tff(c_3809, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_840])).
% 7.77/2.51  tff(c_3816, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_3809, c_6])).
% 7.77/2.51  tff(c_3824, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_3816])).
% 7.77/2.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.77/2.51  
% 7.77/2.51  Inference rules
% 7.77/2.51  ----------------------
% 7.77/2.51  #Ref     : 0
% 7.77/2.51  #Sup     : 801
% 7.77/2.51  #Fact    : 0
% 7.77/2.51  #Define  : 0
% 7.77/2.51  #Split   : 22
% 7.77/2.51  #Chain   : 0
% 7.77/2.51  #Close   : 0
% 7.77/2.51  
% 7.77/2.51  Ordering : KBO
% 7.77/2.51  
% 7.77/2.51  Simplification rules
% 7.77/2.51  ----------------------
% 7.77/2.51  #Subsume      : 182
% 7.77/2.51  #Demod        : 805
% 7.77/2.51  #Tautology    : 251
% 7.77/2.51  #SimpNegUnit  : 41
% 7.77/2.51  #BackRed      : 65
% 7.77/2.51  
% 7.77/2.51  #Partial instantiations: 0
% 7.77/2.51  #Strategies tried      : 1
% 7.77/2.51  
% 7.77/2.51  Timing (in seconds)
% 7.77/2.51  ----------------------
% 7.77/2.52  Preprocessing        : 0.42
% 7.77/2.52  Parsing              : 0.21
% 7.77/2.52  CNF conversion       : 0.04
% 7.77/2.52  Main loop            : 1.29
% 7.77/2.52  Inferencing          : 0.42
% 7.77/2.52  Reduction            : 0.43
% 7.77/2.52  Demodulation         : 0.30
% 7.77/2.52  BG Simplification    : 0.05
% 7.77/2.52  Subsumption          : 0.29
% 7.77/2.52  Abstraction          : 0.05
% 7.77/2.52  MUC search           : 0.00
% 7.77/2.52  Cooper               : 0.00
% 7.77/2.52  Total                : 1.76
% 7.77/2.52  Index Insertion      : 0.00
% 7.77/2.52  Index Deletion       : 0.00
% 7.77/2.52  Index Matching       : 0.00
% 7.77/2.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
