%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:26 EST 2020

% Result     : Theorem 3.45s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 326 expanded)
%              Number of leaves         :   44 ( 125 expanded)
%              Depth                    :   14
%              Number of atoms          :  209 ( 710 expanded)
%              Number of equality atoms :  113 ( 337 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k3_mcart_1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_157,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_117,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_30,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_32,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(D,k1_enumset1(A,B,C))
    <=> ~ ( D != k1_xboole_0
          & D != k1_tarski(A)
          & D != k1_tarski(B)
          & D != k1_tarski(C)
          & D != k2_tarski(A,B)
          & D != k2_tarski(B,C)
          & D != k2_tarski(A,C)
          & D != k1_enumset1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).

tff(f_78,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_63,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_133,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_145,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_103,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_149,plain,(
    ! [C_77,A_78,B_79] :
      ( v1_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_157,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_149])).

tff(c_44,plain,(
    ! [A_18] :
      ( k1_relat_1(A_18) != k1_xboole_0
      | k1_xboole_0 = A_18
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_174,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_157,c_44])).

tff(c_190,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_174])).

tff(c_76,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_48,plain,(
    ! [B_21,A_20] :
      ( k1_tarski(k1_funct_1(B_21,A_20)) = k2_relat_1(B_21)
      | k1_tarski(A_20) != k1_relat_1(B_21)
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_317,plain,(
    ! [A_130,B_131,C_132] :
      ( k2_relset_1(A_130,B_131,C_132) = k2_relat_1(C_132)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_325,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_317])).

tff(c_68,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') != k1_tarski(k1_funct_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_365,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_68])).

tff(c_372,plain,
    ( k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_365])).

tff(c_375,plain,(
    k1_tarski('#skF_2') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_76,c_372])).

tff(c_225,plain,(
    ! [C_94,A_95,B_96] :
      ( v4_relat_1(C_94,A_95)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_233,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_72,c_225])).

tff(c_6,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_36,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k1_relat_1(B_17),A_16)
      | ~ v4_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8,plain,(
    ! [A_3,B_4] : k1_enumset1(A_3,A_3,B_4) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_502,plain,(
    ! [A_177,B_178,C_179,D_180] :
      ( k1_enumset1(A_177,B_178,C_179) = D_180
      | k2_tarski(A_177,C_179) = D_180
      | k2_tarski(B_178,C_179) = D_180
      | k2_tarski(A_177,B_178) = D_180
      | k1_tarski(C_179) = D_180
      | k1_tarski(B_178) = D_180
      | k1_tarski(A_177) = D_180
      | k1_xboole_0 = D_180
      | ~ r1_tarski(D_180,k1_enumset1(A_177,B_178,C_179)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_536,plain,(
    ! [A_3,B_4,D_180] :
      ( k1_enumset1(A_3,A_3,B_4) = D_180
      | k2_tarski(A_3,B_4) = D_180
      | k2_tarski(A_3,B_4) = D_180
      | k2_tarski(A_3,A_3) = D_180
      | k1_tarski(B_4) = D_180
      | k1_tarski(A_3) = D_180
      | k1_tarski(A_3) = D_180
      | k1_xboole_0 = D_180
      | ~ r1_tarski(D_180,k2_tarski(A_3,B_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_502])).

tff(c_820,plain,(
    ! [A_216,B_217,D_218] :
      ( k2_tarski(A_216,B_217) = D_218
      | k2_tarski(A_216,B_217) = D_218
      | k2_tarski(A_216,B_217) = D_218
      | k1_tarski(A_216) = D_218
      | k1_tarski(B_217) = D_218
      | k1_tarski(A_216) = D_218
      | k1_tarski(A_216) = D_218
      | k1_xboole_0 = D_218
      | ~ r1_tarski(D_218,k2_tarski(A_216,B_217)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8,c_536])).

tff(c_860,plain,(
    ! [A_221,B_222,B_223] :
      ( k2_tarski(A_221,B_222) = k1_relat_1(B_223)
      | k1_tarski(B_222) = k1_relat_1(B_223)
      | k1_tarski(A_221) = k1_relat_1(B_223)
      | k1_relat_1(B_223) = k1_xboole_0
      | ~ v4_relat_1(B_223,k2_tarski(A_221,B_222))
      | ~ v1_relat_1(B_223) ) ),
    inference(resolution,[status(thm)],[c_36,c_820])).

tff(c_867,plain,(
    ! [A_2,B_223] :
      ( k2_tarski(A_2,A_2) = k1_relat_1(B_223)
      | k1_tarski(A_2) = k1_relat_1(B_223)
      | k1_tarski(A_2) = k1_relat_1(B_223)
      | k1_relat_1(B_223) = k1_xboole_0
      | ~ v4_relat_1(B_223,k1_tarski(A_2))
      | ~ v1_relat_1(B_223) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_860])).

tff(c_872,plain,(
    ! [A_224,B_225] :
      ( k1_tarski(A_224) = k1_relat_1(B_225)
      | k1_tarski(A_224) = k1_relat_1(B_225)
      | k1_tarski(A_224) = k1_relat_1(B_225)
      | k1_relat_1(B_225) = k1_xboole_0
      | ~ v4_relat_1(B_225,k1_tarski(A_224))
      | ~ v1_relat_1(B_225) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_867])).

tff(c_878,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_233,c_872])).

tff(c_885,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_878])).

tff(c_887,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_190,c_375,c_885])).

tff(c_888,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_38,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_898,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_888,c_888,c_38])).

tff(c_42,plain,(
    ! [A_18] :
      ( k2_relat_1(A_18) != k1_xboole_0
      | k1_xboole_0 = A_18
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_173,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_157,c_42])).

tff(c_189,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_173])).

tff(c_890,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_888,c_189])).

tff(c_933,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_898,c_890])).

tff(c_934,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_173])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_944,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_934,c_4])).

tff(c_40,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_945,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_934,c_934,c_40])).

tff(c_935,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_173])).

tff(c_959,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_934,c_935])).

tff(c_1139,plain,(
    ! [B_287,A_288] :
      ( k1_tarski(k1_funct_1(B_287,A_288)) = k2_relat_1(B_287)
      | k1_tarski(A_288) != k1_relat_1(B_287)
      | ~ v1_funct_1(B_287)
      | ~ v1_relat_1(B_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_30,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_942,plain,(
    ! [A_12] : m1_subset_1('#skF_4',k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_934,c_30])).

tff(c_1124,plain,(
    ! [A_282,B_283,C_284] :
      ( k2_relset_1(A_282,B_283,C_284) = k2_relat_1(C_284)
      | ~ m1_subset_1(C_284,k1_zfmisc_1(k2_zfmisc_1(A_282,B_283))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1128,plain,(
    ! [A_282,B_283] : k2_relset_1(A_282,B_283,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_942,c_1124])).

tff(c_1130,plain,(
    ! [A_282,B_283] : k2_relset_1(A_282,B_283,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_959,c_1128])).

tff(c_1131,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1130,c_68])).

tff(c_1145,plain,
    ( k2_relat_1('#skF_4') != '#skF_4'
    | k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1139,c_1131])).

tff(c_1172,plain,(
    k1_tarski('#skF_2') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_76,c_945,c_959,c_1145])).

tff(c_70,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_947,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_934,c_70])).

tff(c_74,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_60,plain,(
    ! [A_33] :
      ( r2_hidden('#skF_1'(A_33),A_33)
      | k1_xboole_0 = A_33 ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_940,plain,(
    ! [A_33] :
      ( r2_hidden('#skF_1'(A_33),A_33)
      | A_33 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_934,c_60])).

tff(c_66,plain,(
    ! [D_50,C_49,A_47,B_48] :
      ( r2_hidden(k1_funct_1(D_50,C_49),k2_relset_1(A_47,B_48,D_50))
      | k1_xboole_0 = B_48
      | ~ r2_hidden(C_49,A_47)
      | ~ m1_subset_1(D_50,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48)))
      | ~ v1_funct_2(D_50,A_47,B_48)
      | ~ v1_funct_1(D_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_1191,plain,(
    ! [D_292,C_293,A_294,B_295] :
      ( r2_hidden(k1_funct_1(D_292,C_293),k2_relset_1(A_294,B_295,D_292))
      | B_295 = '#skF_4'
      | ~ r2_hidden(C_293,A_294)
      | ~ m1_subset_1(D_292,k1_zfmisc_1(k2_zfmisc_1(A_294,B_295)))
      | ~ v1_funct_2(D_292,A_294,B_295)
      | ~ v1_funct_1(D_292) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_934,c_66])).

tff(c_1201,plain,(
    ! [C_293,B_283,A_282] :
      ( r2_hidden(k1_funct_1('#skF_4',C_293),'#skF_4')
      | B_283 = '#skF_4'
      | ~ r2_hidden(C_293,A_282)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_282,B_283)))
      | ~ v1_funct_2('#skF_4',A_282,B_283)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1130,c_1191])).

tff(c_1207,plain,(
    ! [C_296,B_297,A_298] :
      ( r2_hidden(k1_funct_1('#skF_4',C_296),'#skF_4')
      | B_297 = '#skF_4'
      | ~ r2_hidden(C_296,A_298)
      | ~ v1_funct_2('#skF_4',A_298,B_297) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_942,c_1201])).

tff(c_1214,plain,(
    ! [A_299,B_300] :
      ( r2_hidden(k1_funct_1('#skF_4','#skF_1'(A_299)),'#skF_4')
      | B_300 = '#skF_4'
      | ~ v1_funct_2('#skF_4',A_299,B_300)
      | A_299 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_940,c_1207])).

tff(c_1216,plain,
    ( r2_hidden(k1_funct_1('#skF_4','#skF_1'(k1_tarski('#skF_2'))),'#skF_4')
    | '#skF_3' = '#skF_4'
    | k1_tarski('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_74,c_1214])).

tff(c_1219,plain,(
    r2_hidden(k1_funct_1('#skF_4','#skF_1'(k1_tarski('#skF_2'))),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1172,c_947,c_1216])).

tff(c_50,plain,(
    ! [B_23,A_22] :
      ( ~ r1_tarski(B_23,A_22)
      | ~ r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1230,plain,(
    ~ r1_tarski('#skF_4',k1_funct_1('#skF_4','#skF_1'(k1_tarski('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_1219,c_50])).

tff(c_1240,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_944,c_1230])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:06:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.45/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/1.61  
% 3.45/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/1.61  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k3_mcart_1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.45/1.61  
% 3.45/1.61  %Foreground sorts:
% 3.45/1.61  
% 3.45/1.61  
% 3.45/1.61  %Background operators:
% 3.45/1.61  
% 3.45/1.61  
% 3.45/1.61  %Foreground operators:
% 3.45/1.61  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.45/1.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.45/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.45/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.45/1.61  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.45/1.61  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.45/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.45/1.61  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.45/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.45/1.61  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.45/1.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.45/1.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.45/1.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.45/1.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.45/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.45/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.45/1.61  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.45/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.45/1.61  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.45/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.45/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.45/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.45/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.45/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.45/1.61  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.45/1.61  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.45/1.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.45/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.45/1.61  
% 3.85/1.63  tff(f_157, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 3.85/1.63  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.85/1.63  tff(f_86, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.85/1.63  tff(f_98, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 3.85/1.63  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.85/1.63  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.85/1.63  tff(f_30, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.85/1.63  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.85/1.63  tff(f_32, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.85/1.63  tff(f_61, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 3.85/1.63  tff(f_78, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.85/1.63  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.85/1.63  tff(f_63, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.85/1.63  tff(f_133, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 3.85/1.63  tff(f_145, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 3.85/1.63  tff(f_103, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.85/1.63  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.85/1.63  tff(c_149, plain, (![C_77, A_78, B_79]: (v1_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.85/1.63  tff(c_157, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_149])).
% 3.85/1.63  tff(c_44, plain, (![A_18]: (k1_relat_1(A_18)!=k1_xboole_0 | k1_xboole_0=A_18 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.85/1.63  tff(c_174, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_157, c_44])).
% 3.85/1.63  tff(c_190, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_174])).
% 3.85/1.63  tff(c_76, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.85/1.63  tff(c_48, plain, (![B_21, A_20]: (k1_tarski(k1_funct_1(B_21, A_20))=k2_relat_1(B_21) | k1_tarski(A_20)!=k1_relat_1(B_21) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.85/1.63  tff(c_317, plain, (![A_130, B_131, C_132]: (k2_relset_1(A_130, B_131, C_132)=k2_relat_1(C_132) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.85/1.63  tff(c_325, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_317])).
% 3.85/1.63  tff(c_68, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')!=k1_tarski(k1_funct_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.85/1.63  tff(c_365, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_325, c_68])).
% 3.85/1.63  tff(c_372, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_48, c_365])).
% 3.85/1.63  tff(c_375, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_157, c_76, c_372])).
% 3.85/1.63  tff(c_225, plain, (![C_94, A_95, B_96]: (v4_relat_1(C_94, A_95) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.85/1.63  tff(c_233, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_72, c_225])).
% 3.85/1.63  tff(c_6, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.85/1.63  tff(c_36, plain, (![B_17, A_16]: (r1_tarski(k1_relat_1(B_17), A_16) | ~v4_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.85/1.63  tff(c_8, plain, (![A_3, B_4]: (k1_enumset1(A_3, A_3, B_4)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.85/1.63  tff(c_502, plain, (![A_177, B_178, C_179, D_180]: (k1_enumset1(A_177, B_178, C_179)=D_180 | k2_tarski(A_177, C_179)=D_180 | k2_tarski(B_178, C_179)=D_180 | k2_tarski(A_177, B_178)=D_180 | k1_tarski(C_179)=D_180 | k1_tarski(B_178)=D_180 | k1_tarski(A_177)=D_180 | k1_xboole_0=D_180 | ~r1_tarski(D_180, k1_enumset1(A_177, B_178, C_179)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.85/1.63  tff(c_536, plain, (![A_3, B_4, D_180]: (k1_enumset1(A_3, A_3, B_4)=D_180 | k2_tarski(A_3, B_4)=D_180 | k2_tarski(A_3, B_4)=D_180 | k2_tarski(A_3, A_3)=D_180 | k1_tarski(B_4)=D_180 | k1_tarski(A_3)=D_180 | k1_tarski(A_3)=D_180 | k1_xboole_0=D_180 | ~r1_tarski(D_180, k2_tarski(A_3, B_4)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_502])).
% 3.85/1.63  tff(c_820, plain, (![A_216, B_217, D_218]: (k2_tarski(A_216, B_217)=D_218 | k2_tarski(A_216, B_217)=D_218 | k2_tarski(A_216, B_217)=D_218 | k1_tarski(A_216)=D_218 | k1_tarski(B_217)=D_218 | k1_tarski(A_216)=D_218 | k1_tarski(A_216)=D_218 | k1_xboole_0=D_218 | ~r1_tarski(D_218, k2_tarski(A_216, B_217)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8, c_536])).
% 3.85/1.63  tff(c_860, plain, (![A_221, B_222, B_223]: (k2_tarski(A_221, B_222)=k1_relat_1(B_223) | k1_tarski(B_222)=k1_relat_1(B_223) | k1_tarski(A_221)=k1_relat_1(B_223) | k1_relat_1(B_223)=k1_xboole_0 | ~v4_relat_1(B_223, k2_tarski(A_221, B_222)) | ~v1_relat_1(B_223))), inference(resolution, [status(thm)], [c_36, c_820])).
% 3.85/1.63  tff(c_867, plain, (![A_2, B_223]: (k2_tarski(A_2, A_2)=k1_relat_1(B_223) | k1_tarski(A_2)=k1_relat_1(B_223) | k1_tarski(A_2)=k1_relat_1(B_223) | k1_relat_1(B_223)=k1_xboole_0 | ~v4_relat_1(B_223, k1_tarski(A_2)) | ~v1_relat_1(B_223))), inference(superposition, [status(thm), theory('equality')], [c_6, c_860])).
% 3.85/1.63  tff(c_872, plain, (![A_224, B_225]: (k1_tarski(A_224)=k1_relat_1(B_225) | k1_tarski(A_224)=k1_relat_1(B_225) | k1_tarski(A_224)=k1_relat_1(B_225) | k1_relat_1(B_225)=k1_xboole_0 | ~v4_relat_1(B_225, k1_tarski(A_224)) | ~v1_relat_1(B_225))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_867])).
% 3.85/1.63  tff(c_878, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_233, c_872])).
% 3.85/1.63  tff(c_885, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_157, c_878])).
% 3.85/1.63  tff(c_887, plain, $false, inference(negUnitSimplification, [status(thm)], [c_190, c_375, c_885])).
% 3.85/1.63  tff(c_888, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_174])).
% 3.85/1.63  tff(c_38, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.85/1.63  tff(c_898, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_888, c_888, c_38])).
% 3.85/1.63  tff(c_42, plain, (![A_18]: (k2_relat_1(A_18)!=k1_xboole_0 | k1_xboole_0=A_18 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.85/1.63  tff(c_173, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_157, c_42])).
% 3.85/1.63  tff(c_189, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_173])).
% 3.85/1.63  tff(c_890, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_888, c_189])).
% 3.85/1.63  tff(c_933, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_898, c_890])).
% 3.85/1.63  tff(c_934, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_173])).
% 3.85/1.63  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 3.85/1.63  tff(c_944, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_934, c_4])).
% 3.85/1.63  tff(c_40, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.85/1.63  tff(c_945, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_934, c_934, c_40])).
% 3.85/1.63  tff(c_935, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_173])).
% 3.85/1.63  tff(c_959, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_934, c_935])).
% 3.85/1.63  tff(c_1139, plain, (![B_287, A_288]: (k1_tarski(k1_funct_1(B_287, A_288))=k2_relat_1(B_287) | k1_tarski(A_288)!=k1_relat_1(B_287) | ~v1_funct_1(B_287) | ~v1_relat_1(B_287))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.85/1.63  tff(c_30, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.85/1.63  tff(c_942, plain, (![A_12]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_934, c_30])).
% 3.85/1.63  tff(c_1124, plain, (![A_282, B_283, C_284]: (k2_relset_1(A_282, B_283, C_284)=k2_relat_1(C_284) | ~m1_subset_1(C_284, k1_zfmisc_1(k2_zfmisc_1(A_282, B_283))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.85/1.63  tff(c_1128, plain, (![A_282, B_283]: (k2_relset_1(A_282, B_283, '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_942, c_1124])).
% 3.85/1.63  tff(c_1130, plain, (![A_282, B_283]: (k2_relset_1(A_282, B_283, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_959, c_1128])).
% 3.85/1.63  tff(c_1131, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1130, c_68])).
% 3.85/1.63  tff(c_1145, plain, (k2_relat_1('#skF_4')!='#skF_4' | k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1139, c_1131])).
% 3.85/1.63  tff(c_1172, plain, (k1_tarski('#skF_2')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_157, c_76, c_945, c_959, c_1145])).
% 3.85/1.63  tff(c_70, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.85/1.63  tff(c_947, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_934, c_70])).
% 3.85/1.63  tff(c_74, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.85/1.63  tff(c_60, plain, (![A_33]: (r2_hidden('#skF_1'(A_33), A_33) | k1_xboole_0=A_33)), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.85/1.63  tff(c_940, plain, (![A_33]: (r2_hidden('#skF_1'(A_33), A_33) | A_33='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_934, c_60])).
% 3.85/1.63  tff(c_66, plain, (![D_50, C_49, A_47, B_48]: (r2_hidden(k1_funct_1(D_50, C_49), k2_relset_1(A_47, B_48, D_50)) | k1_xboole_0=B_48 | ~r2_hidden(C_49, A_47) | ~m1_subset_1(D_50, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))) | ~v1_funct_2(D_50, A_47, B_48) | ~v1_funct_1(D_50))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.85/1.63  tff(c_1191, plain, (![D_292, C_293, A_294, B_295]: (r2_hidden(k1_funct_1(D_292, C_293), k2_relset_1(A_294, B_295, D_292)) | B_295='#skF_4' | ~r2_hidden(C_293, A_294) | ~m1_subset_1(D_292, k1_zfmisc_1(k2_zfmisc_1(A_294, B_295))) | ~v1_funct_2(D_292, A_294, B_295) | ~v1_funct_1(D_292))), inference(demodulation, [status(thm), theory('equality')], [c_934, c_66])).
% 3.85/1.63  tff(c_1201, plain, (![C_293, B_283, A_282]: (r2_hidden(k1_funct_1('#skF_4', C_293), '#skF_4') | B_283='#skF_4' | ~r2_hidden(C_293, A_282) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_282, B_283))) | ~v1_funct_2('#skF_4', A_282, B_283) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1130, c_1191])).
% 3.85/1.63  tff(c_1207, plain, (![C_296, B_297, A_298]: (r2_hidden(k1_funct_1('#skF_4', C_296), '#skF_4') | B_297='#skF_4' | ~r2_hidden(C_296, A_298) | ~v1_funct_2('#skF_4', A_298, B_297))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_942, c_1201])).
% 3.85/1.63  tff(c_1214, plain, (![A_299, B_300]: (r2_hidden(k1_funct_1('#skF_4', '#skF_1'(A_299)), '#skF_4') | B_300='#skF_4' | ~v1_funct_2('#skF_4', A_299, B_300) | A_299='#skF_4')), inference(resolution, [status(thm)], [c_940, c_1207])).
% 3.85/1.63  tff(c_1216, plain, (r2_hidden(k1_funct_1('#skF_4', '#skF_1'(k1_tarski('#skF_2'))), '#skF_4') | '#skF_3'='#skF_4' | k1_tarski('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_74, c_1214])).
% 3.85/1.63  tff(c_1219, plain, (r2_hidden(k1_funct_1('#skF_4', '#skF_1'(k1_tarski('#skF_2'))), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_1172, c_947, c_1216])).
% 3.85/1.63  tff(c_50, plain, (![B_23, A_22]: (~r1_tarski(B_23, A_22) | ~r2_hidden(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.85/1.63  tff(c_1230, plain, (~r1_tarski('#skF_4', k1_funct_1('#skF_4', '#skF_1'(k1_tarski('#skF_2'))))), inference(resolution, [status(thm)], [c_1219, c_50])).
% 3.85/1.63  tff(c_1240, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_944, c_1230])).
% 3.85/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.63  
% 3.85/1.63  Inference rules
% 3.85/1.63  ----------------------
% 3.85/1.63  #Ref     : 0
% 3.85/1.63  #Sup     : 241
% 3.85/1.63  #Fact    : 0
% 3.85/1.63  #Define  : 0
% 3.85/1.63  #Split   : 3
% 3.85/1.63  #Chain   : 0
% 3.85/1.63  #Close   : 0
% 3.85/1.63  
% 3.85/1.63  Ordering : KBO
% 3.85/1.63  
% 3.85/1.63  Simplification rules
% 3.85/1.63  ----------------------
% 3.85/1.63  #Subsume      : 33
% 3.85/1.63  #Demod        : 243
% 3.85/1.63  #Tautology    : 133
% 3.85/1.63  #SimpNegUnit  : 12
% 3.85/1.63  #BackRed      : 36
% 3.85/1.63  
% 3.85/1.63  #Partial instantiations: 0
% 3.85/1.63  #Strategies tried      : 1
% 3.85/1.63  
% 3.85/1.63  Timing (in seconds)
% 3.85/1.63  ----------------------
% 3.85/1.63  Preprocessing        : 0.36
% 3.85/1.63  Parsing              : 0.20
% 3.85/1.63  CNF conversion       : 0.02
% 3.85/1.63  Main loop            : 0.47
% 3.85/1.63  Inferencing          : 0.17
% 3.85/1.63  Reduction            : 0.16
% 3.85/1.63  Demodulation         : 0.11
% 3.85/1.63  BG Simplification    : 0.02
% 3.85/1.63  Subsumption          : 0.09
% 3.85/1.63  Abstraction          : 0.02
% 3.85/1.63  MUC search           : 0.00
% 3.85/1.63  Cooper               : 0.00
% 3.85/1.63  Total                : 0.87
% 3.85/1.63  Index Insertion      : 0.00
% 3.85/1.63  Index Deletion       : 0.00
% 3.85/1.63  Index Matching       : 0.00
% 3.85/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
