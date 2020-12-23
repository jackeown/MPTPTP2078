%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:43 EST 2020

% Result     : Theorem 4.01s
% Output     : CNFRefutation 4.47s
% Verified   : 
% Statistics : Number of formulae       :  182 (1263 expanded)
%              Number of leaves         :   37 ( 403 expanded)
%              Depth                    :   15
%              Number of atoms          :  347 (3451 expanded)
%              Number of equality atoms :  124 (1386 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_59,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_124,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( v2_funct_1(B)
        <=> ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A)
                & k1_funct_1(B,C) = k1_funct_1(B,D) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_funct_2)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_106,axiom,(
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

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_28,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_60,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_163,plain,(
    ! [B_55,A_56] :
      ( v1_relat_1(B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_56))
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_169,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_4')) ),
    inference(resolution,[status(thm)],[c_60,c_163])).

tff(c_173,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_169])).

tff(c_64,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_814,plain,(
    ! [A_134] :
      ( '#skF_2'(A_134) != '#skF_3'(A_134)
      | v2_funct_1(A_134)
      | ~ v1_funct_1(A_134)
      | ~ v1_relat_1(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_66,plain,
    ( '#skF_7' != '#skF_6'
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_92,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_817,plain,
    ( '#skF_2'('#skF_5') != '#skF_3'('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_814,c_92])).

tff(c_820,plain,(
    '#skF_2'('#skF_5') != '#skF_3'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_64,c_817])).

tff(c_62,plain,(
    v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_203,plain,(
    ! [A_61] :
      ( '#skF_2'(A_61) != '#skF_3'(A_61)
      | v2_funct_1(A_61)
      | ~ v1_funct_1(A_61)
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_206,plain,
    ( '#skF_2'('#skF_5') != '#skF_3'('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_203,c_92])).

tff(c_209,plain,(
    '#skF_2'('#skF_5') != '#skF_3'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_64,c_206])).

tff(c_256,plain,(
    ! [A_70,B_71,C_72] :
      ( k1_relset_1(A_70,B_71,C_72) = k1_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_271,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_256])).

tff(c_563,plain,(
    ! [B_119,A_120,C_121] :
      ( k1_xboole_0 = B_119
      | k1_relset_1(A_120,B_119,C_121) = A_120
      | ~ v1_funct_2(C_121,A_120,B_119)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_120,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_570,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_4','#skF_4','#skF_5') = '#skF_4'
    | ~ v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_563])).

tff(c_580,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_271,c_570])).

tff(c_591,plain,(
    k1_relat_1('#skF_5') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_580])).

tff(c_36,plain,(
    ! [A_17] :
      ( r2_hidden('#skF_3'(A_17),k1_relat_1(A_17))
      | v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_602,plain,
    ( r2_hidden('#skF_3'('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_591,c_36])).

tff(c_616,plain,
    ( r2_hidden('#skF_3'('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_64,c_602])).

tff(c_617,plain,(
    r2_hidden('#skF_3'('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_616])).

tff(c_38,plain,(
    ! [A_17] :
      ( r2_hidden('#skF_2'(A_17),k1_relat_1(A_17))
      | v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_608,plain,
    ( r2_hidden('#skF_2'('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_591,c_38])).

tff(c_622,plain,
    ( r2_hidden('#skF_2'('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_64,c_608])).

tff(c_623,plain,(
    r2_hidden('#skF_2'('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_622])).

tff(c_412,plain,(
    ! [A_102] :
      ( k1_funct_1(A_102,'#skF_2'(A_102)) = k1_funct_1(A_102,'#skF_3'(A_102))
      | v2_funct_1(A_102)
      | ~ v1_funct_1(A_102)
      | ~ v1_relat_1(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_84,plain,(
    ! [D_38,C_37] :
      ( v2_funct_1('#skF_5')
      | D_38 = C_37
      | k1_funct_1('#skF_5',D_38) != k1_funct_1('#skF_5',C_37)
      | ~ r2_hidden(D_38,'#skF_4')
      | ~ r2_hidden(C_37,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_238,plain,(
    ! [D_38,C_37] :
      ( D_38 = C_37
      | k1_funct_1('#skF_5',D_38) != k1_funct_1('#skF_5',C_37)
      | ~ r2_hidden(D_38,'#skF_4')
      | ~ r2_hidden(C_37,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_84])).

tff(c_418,plain,(
    ! [C_37] :
      ( C_37 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',C_37) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | ~ r2_hidden(C_37,'#skF_4')
      | v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_412,c_238])).

tff(c_427,plain,(
    ! [C_37] :
      ( C_37 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',C_37) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | ~ r2_hidden(C_37,'#skF_4')
      | v2_funct_1('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_64,c_418])).

tff(c_428,plain,(
    ! [C_37] :
      ( C_37 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',C_37) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | ~ r2_hidden(C_37,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_427])).

tff(c_704,plain,(
    ! [C_37] :
      ( C_37 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',C_37) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden(C_37,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_623,c_428])).

tff(c_707,plain,
    ( '#skF_2'('#skF_5') = '#skF_3'('#skF_5')
    | ~ r2_hidden('#skF_3'('#skF_5'),'#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_704])).

tff(c_709,plain,(
    '#skF_2'('#skF_5') = '#skF_3'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_617,c_707])).

tff(c_711,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_209,c_709])).

tff(c_712,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_580])).

tff(c_14,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_736,plain,(
    ! [A_7] : r1_tarski('#skF_4',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_712,c_14])).

tff(c_18,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_735,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_712,c_712,c_18])).

tff(c_128,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(A_50,B_51)
      | ~ m1_subset_1(A_50,k1_zfmisc_1(B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_136,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_4','#skF_4')) ),
    inference(resolution,[status(thm)],[c_60,c_128])).

tff(c_137,plain,(
    ! [B_52,A_53] :
      ( B_52 = A_53
      | ~ r1_tarski(B_52,A_53)
      | ~ r1_tarski(A_53,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_144,plain,
    ( k2_zfmisc_1('#skF_4','#skF_4') = '#skF_5'
    | ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_136,c_137])).

tff(c_201,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_144])).

tff(c_757,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_735,c_201])).

tff(c_762,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_736,c_757])).

tff(c_763,plain,(
    k2_zfmisc_1('#skF_4','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_766,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_763,c_60])).

tff(c_838,plain,(
    ! [A_140,B_141,C_142] :
      ( k1_relset_1(A_140,B_141,C_142) = k1_relat_1(C_142)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_920,plain,(
    ! [C_155] :
      ( k1_relset_1('#skF_4','#skF_4',C_155) = k1_relat_1(C_155)
      | ~ m1_subset_1(C_155,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_763,c_838])).

tff(c_928,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_766,c_920])).

tff(c_1098,plain,(
    ! [B_183,A_184,C_185] :
      ( k1_xboole_0 = B_183
      | k1_relset_1(A_184,B_183,C_185) = A_184
      | ~ v1_funct_2(C_185,A_184,B_183)
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(A_184,B_183))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1101,plain,(
    ! [C_185] :
      ( k1_xboole_0 = '#skF_4'
      | k1_relset_1('#skF_4','#skF_4',C_185) = '#skF_4'
      | ~ v1_funct_2(C_185,'#skF_4','#skF_4')
      | ~ m1_subset_1(C_185,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_763,c_1098])).

tff(c_1114,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1101])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( k1_xboole_0 = B_9
      | k1_xboole_0 = A_8
      | k2_zfmisc_1(A_8,B_9) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_771,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_763,c_16])).

tff(c_813,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_771])).

tff(c_1143,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1114,c_813])).

tff(c_1150,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1114,c_1114,c_18])).

tff(c_1177,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1150,c_763])).

tff(c_1179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1143,c_1177])).

tff(c_1198,plain,(
    ! [C_193] :
      ( k1_relset_1('#skF_4','#skF_4',C_193) = '#skF_4'
      | ~ v1_funct_2(C_193,'#skF_4','#skF_4')
      | ~ m1_subset_1(C_193,k1_zfmisc_1('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_1101])).

tff(c_1201,plain,
    ( k1_relset_1('#skF_4','#skF_4','#skF_5') = '#skF_4'
    | ~ v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_766,c_1198])).

tff(c_1208,plain,(
    k1_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_928,c_1201])).

tff(c_1220,plain,
    ( r2_hidden('#skF_3'('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1208,c_36])).

tff(c_1234,plain,
    ( r2_hidden('#skF_3'('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_64,c_1220])).

tff(c_1235,plain,(
    r2_hidden('#skF_3'('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_1234])).

tff(c_1226,plain,
    ( r2_hidden('#skF_2'('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1208,c_38])).

tff(c_1240,plain,
    ( r2_hidden('#skF_2'('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_64,c_1226])).

tff(c_1241,plain,(
    r2_hidden('#skF_2'('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_1240])).

tff(c_1029,plain,(
    ! [A_176] :
      ( k1_funct_1(A_176,'#skF_2'(A_176)) = k1_funct_1(A_176,'#skF_3'(A_176))
      | v2_funct_1(A_176)
      | ~ v1_funct_1(A_176)
      | ~ v1_relat_1(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_827,plain,(
    ! [D_38,C_37] :
      ( D_38 = C_37
      | k1_funct_1('#skF_5',D_38) != k1_funct_1('#skF_5',C_37)
      | ~ r2_hidden(D_38,'#skF_4')
      | ~ r2_hidden(C_37,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_84])).

tff(c_1035,plain,(
    ! [C_37] :
      ( C_37 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',C_37) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | ~ r2_hidden(C_37,'#skF_4')
      | v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1029,c_827])).

tff(c_1044,plain,(
    ! [C_37] :
      ( C_37 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',C_37) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | ~ r2_hidden(C_37,'#skF_4')
      | v2_funct_1('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_64,c_1035])).

tff(c_1045,plain,(
    ! [C_37] :
      ( C_37 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',C_37) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | ~ r2_hidden(C_37,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_1044])).

tff(c_1338,plain,(
    ! [C_37] :
      ( C_37 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',C_37) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden(C_37,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1241,c_1045])).

tff(c_1341,plain,
    ( '#skF_2'('#skF_5') = '#skF_3'('#skF_5')
    | ~ r2_hidden('#skF_3'('#skF_5'),'#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1338])).

tff(c_1343,plain,(
    '#skF_2'('#skF_5') = '#skF_3'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1235,c_1341])).

tff(c_1345,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_820,c_1343])).

tff(c_1347,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_771])).

tff(c_1346,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_771])).

tff(c_1382,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1347,c_1347,c_1346])).

tff(c_1383,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1382])).

tff(c_1399,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1383,c_92])).

tff(c_1397,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1383,c_173])).

tff(c_1400,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1383,c_64])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1356,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1347,c_6])).

tff(c_1393,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1383,c_1356])).

tff(c_1395,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1383,c_1383,c_766])).

tff(c_1355,plain,(
    ! [A_7] : r1_tarski('#skF_5',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1347,c_14])).

tff(c_1392,plain,(
    ! [A_7] : r1_tarski('#skF_4',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1383,c_1355])).

tff(c_24,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1519,plain,(
    ! [A_214,B_215,C_216] :
      ( k1_relset_1(A_214,B_215,C_216) = k1_relat_1(C_216)
      | ~ m1_subset_1(C_216,k1_zfmisc_1(k2_zfmisc_1(A_214,B_215))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1635,plain,(
    ! [A_235,B_236,A_237] :
      ( k1_relset_1(A_235,B_236,A_237) = k1_relat_1(A_237)
      | ~ r1_tarski(A_237,k2_zfmisc_1(A_235,B_236)) ) ),
    inference(resolution,[status(thm)],[c_24,c_1519])).

tff(c_1650,plain,(
    ! [A_235,B_236] : k1_relset_1(A_235,B_236,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1392,c_1635])).

tff(c_1398,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1383,c_62])).

tff(c_1394,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1383,c_1347])).

tff(c_20,plain,(
    ! [B_9] : k2_zfmisc_1(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_56,plain,(
    ! [B_31,C_32] :
      ( k1_relset_1(k1_xboole_0,B_31,C_32) = k1_xboole_0
      | ~ v1_funct_2(C_32,k1_xboole_0,B_31)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_86,plain,(
    ! [B_31,C_32] :
      ( k1_relset_1(k1_xboole_0,B_31,C_32) = k1_xboole_0
      | ~ v1_funct_2(C_32,k1_xboole_0,B_31)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_56])).

tff(c_1680,plain,(
    ! [B_245,C_246] :
      ( k1_relset_1('#skF_4',B_245,C_246) = '#skF_4'
      | ~ v1_funct_2(C_246,'#skF_4',B_245)
      | ~ m1_subset_1(C_246,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1394,c_1394,c_1394,c_1394,c_86])).

tff(c_1685,plain,
    ( k1_relset_1('#skF_4','#skF_4','#skF_4') = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1398,c_1680])).

tff(c_1692,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1395,c_1650,c_1685])).

tff(c_1469,plain,(
    ! [A_211] :
      ( r2_hidden('#skF_2'(A_211),k1_relat_1(A_211))
      | v2_funct_1(A_211)
      | ~ v1_funct_1(A_211)
      | ~ v1_relat_1(A_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1473,plain,(
    ! [A_211] :
      ( ~ v1_xboole_0(k1_relat_1(A_211))
      | v2_funct_1(A_211)
      | ~ v1_funct_1(A_211)
      | ~ v1_relat_1(A_211) ) ),
    inference(resolution,[status(thm)],[c_1469,c_2])).

tff(c_1707,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1692,c_1473])).

tff(c_1717,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1397,c_1400,c_1393,c_1707])).

tff(c_1719,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1399,c_1717])).

tff(c_1720,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1382])).

tff(c_1721,plain,(
    '#skF_5' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1382])).

tff(c_1737,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1720,c_1721])).

tff(c_1739,plain,(
    v2_funct_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_72,plain,
    ( r2_hidden('#skF_6','#skF_4')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1769,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1739,c_72])).

tff(c_1770,plain,(
    ! [B_253,A_254] :
      ( ~ r2_hidden(B_253,A_254)
      | ~ v1_xboole_0(A_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1774,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1769,c_1770])).

tff(c_1738,plain,(
    '#skF_7' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_1802,plain,(
    ! [B_260,A_261] :
      ( v1_relat_1(B_260)
      | ~ m1_subset_1(B_260,k1_zfmisc_1(A_261))
      | ~ v1_relat_1(A_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1808,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_4')) ),
    inference(resolution,[status(thm)],[c_60,c_1802])).

tff(c_1812,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1808])).

tff(c_70,plain,
    ( r2_hidden('#skF_7','#skF_4')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1776,plain,(
    r2_hidden('#skF_7','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1739,c_70])).

tff(c_1902,plain,(
    ! [A_274,B_275,C_276] :
      ( k1_relset_1(A_274,B_275,C_276) = k1_relat_1(C_276)
      | ~ m1_subset_1(C_276,k1_zfmisc_1(k2_zfmisc_1(A_274,B_275))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1917,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_1902])).

tff(c_2227,plain,(
    ! [B_321,A_322,C_323] :
      ( k1_xboole_0 = B_321
      | k1_relset_1(A_322,B_321,C_323) = A_322
      | ~ v1_funct_2(C_323,A_322,B_321)
      | ~ m1_subset_1(C_323,k1_zfmisc_1(k2_zfmisc_1(A_322,B_321))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2234,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_4','#skF_4','#skF_5') = '#skF_4'
    | ~ v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_2227])).

tff(c_2244,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1917,c_2234])).

tff(c_2246,plain,(
    k1_relat_1('#skF_5') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2244])).

tff(c_68,plain,
    ( k1_funct_1('#skF_5','#skF_7') = k1_funct_1('#skF_5','#skF_6')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1797,plain,(
    k1_funct_1('#skF_5','#skF_7') = k1_funct_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1739,c_68])).

tff(c_2333,plain,(
    ! [C_330,B_331,A_332] :
      ( C_330 = B_331
      | k1_funct_1(A_332,C_330) != k1_funct_1(A_332,B_331)
      | ~ r2_hidden(C_330,k1_relat_1(A_332))
      | ~ r2_hidden(B_331,k1_relat_1(A_332))
      | ~ v2_funct_1(A_332)
      | ~ v1_funct_1(A_332)
      | ~ v1_relat_1(A_332) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2341,plain,(
    ! [C_330] :
      ( C_330 = '#skF_7'
      | k1_funct_1('#skF_5',C_330) != k1_funct_1('#skF_5','#skF_6')
      | ~ r2_hidden(C_330,k1_relat_1('#skF_5'))
      | ~ r2_hidden('#skF_7',k1_relat_1('#skF_5'))
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1797,c_2333])).

tff(c_2362,plain,(
    ! [C_335] :
      ( C_335 = '#skF_7'
      | k1_funct_1('#skF_5',C_335) != k1_funct_1('#skF_5','#skF_6')
      | ~ r2_hidden(C_335,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1812,c_64,c_1739,c_1776,c_2246,c_2246,c_2341])).

tff(c_2376,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1769,c_2362])).

tff(c_2388,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1738,c_2376])).

tff(c_2389,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2244])).

tff(c_2410,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2389,c_6])).

tff(c_2412,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1774,c_2410])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % DateTime   : Tue Dec  1 13:09:14 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.01/1.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.35/1.79  
% 4.35/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.38/1.79  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3
% 4.38/1.79  
% 4.38/1.79  %Foreground sorts:
% 4.38/1.79  
% 4.38/1.79  
% 4.38/1.79  %Background operators:
% 4.38/1.79  
% 4.38/1.79  
% 4.38/1.79  %Foreground operators:
% 4.38/1.79  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.38/1.79  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.38/1.79  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.38/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.38/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.38/1.79  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.38/1.79  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.38/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.38/1.79  tff('#skF_7', type, '#skF_7': $i).
% 4.38/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.38/1.79  tff('#skF_5', type, '#skF_5': $i).
% 4.38/1.79  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.38/1.79  tff('#skF_6', type, '#skF_6': $i).
% 4.38/1.79  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.38/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.38/1.79  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.38/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.38/1.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.38/1.79  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.38/1.79  tff('#skF_4', type, '#skF_4': $i).
% 4.38/1.79  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.38/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.38/1.79  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.38/1.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.38/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.38/1.79  
% 4.47/1.82  tff(f_59, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.47/1.82  tff(f_124, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) <=> (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_funct_2)).
% 4.47/1.82  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.47/1.82  tff(f_74, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_funct_1)).
% 4.47/1.82  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.47/1.82  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.47/1.82  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.47/1.82  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.47/1.82  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.47/1.82  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.47/1.82  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.47/1.82  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.47/1.82  tff(c_28, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.47/1.82  tff(c_60, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.47/1.82  tff(c_163, plain, (![B_55, A_56]: (v1_relat_1(B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(A_56)) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.47/1.82  tff(c_169, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_60, c_163])).
% 4.47/1.82  tff(c_173, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_169])).
% 4.47/1.82  tff(c_64, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.47/1.82  tff(c_814, plain, (![A_134]: ('#skF_2'(A_134)!='#skF_3'(A_134) | v2_funct_1(A_134) | ~v1_funct_1(A_134) | ~v1_relat_1(A_134))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.47/1.82  tff(c_66, plain, ('#skF_7'!='#skF_6' | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.47/1.82  tff(c_92, plain, (~v2_funct_1('#skF_5')), inference(splitLeft, [status(thm)], [c_66])).
% 4.47/1.82  tff(c_817, plain, ('#skF_2'('#skF_5')!='#skF_3'('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_814, c_92])).
% 4.47/1.82  tff(c_820, plain, ('#skF_2'('#skF_5')!='#skF_3'('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_64, c_817])).
% 4.47/1.82  tff(c_62, plain, (v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.47/1.82  tff(c_203, plain, (![A_61]: ('#skF_2'(A_61)!='#skF_3'(A_61) | v2_funct_1(A_61) | ~v1_funct_1(A_61) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.47/1.82  tff(c_206, plain, ('#skF_2'('#skF_5')!='#skF_3'('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_203, c_92])).
% 4.47/1.82  tff(c_209, plain, ('#skF_2'('#skF_5')!='#skF_3'('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_64, c_206])).
% 4.47/1.82  tff(c_256, plain, (![A_70, B_71, C_72]: (k1_relset_1(A_70, B_71, C_72)=k1_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.47/1.82  tff(c_271, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_256])).
% 4.47/1.82  tff(c_563, plain, (![B_119, A_120, C_121]: (k1_xboole_0=B_119 | k1_relset_1(A_120, B_119, C_121)=A_120 | ~v1_funct_2(C_121, A_120, B_119) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_120, B_119))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.47/1.82  tff(c_570, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_4', '#skF_4', '#skF_5')='#skF_4' | ~v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_60, c_563])).
% 4.47/1.82  tff(c_580, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_271, c_570])).
% 4.47/1.82  tff(c_591, plain, (k1_relat_1('#skF_5')='#skF_4'), inference(splitLeft, [status(thm)], [c_580])).
% 4.47/1.82  tff(c_36, plain, (![A_17]: (r2_hidden('#skF_3'(A_17), k1_relat_1(A_17)) | v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.47/1.82  tff(c_602, plain, (r2_hidden('#skF_3'('#skF_5'), '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_591, c_36])).
% 4.47/1.82  tff(c_616, plain, (r2_hidden('#skF_3'('#skF_5'), '#skF_4') | v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_64, c_602])).
% 4.47/1.82  tff(c_617, plain, (r2_hidden('#skF_3'('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_92, c_616])).
% 4.47/1.82  tff(c_38, plain, (![A_17]: (r2_hidden('#skF_2'(A_17), k1_relat_1(A_17)) | v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.47/1.82  tff(c_608, plain, (r2_hidden('#skF_2'('#skF_5'), '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_591, c_38])).
% 4.47/1.82  tff(c_622, plain, (r2_hidden('#skF_2'('#skF_5'), '#skF_4') | v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_64, c_608])).
% 4.47/1.82  tff(c_623, plain, (r2_hidden('#skF_2'('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_92, c_622])).
% 4.47/1.82  tff(c_412, plain, (![A_102]: (k1_funct_1(A_102, '#skF_2'(A_102))=k1_funct_1(A_102, '#skF_3'(A_102)) | v2_funct_1(A_102) | ~v1_funct_1(A_102) | ~v1_relat_1(A_102))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.47/1.82  tff(c_84, plain, (![D_38, C_37]: (v2_funct_1('#skF_5') | D_38=C_37 | k1_funct_1('#skF_5', D_38)!=k1_funct_1('#skF_5', C_37) | ~r2_hidden(D_38, '#skF_4') | ~r2_hidden(C_37, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.47/1.82  tff(c_238, plain, (![D_38, C_37]: (D_38=C_37 | k1_funct_1('#skF_5', D_38)!=k1_funct_1('#skF_5', C_37) | ~r2_hidden(D_38, '#skF_4') | ~r2_hidden(C_37, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_92, c_84])).
% 4.47/1.82  tff(c_418, plain, (![C_37]: (C_37='#skF_2'('#skF_5') | k1_funct_1('#skF_5', C_37)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | ~r2_hidden(C_37, '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_412, c_238])).
% 4.47/1.82  tff(c_427, plain, (![C_37]: (C_37='#skF_2'('#skF_5') | k1_funct_1('#skF_5', C_37)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | ~r2_hidden(C_37, '#skF_4') | v2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_64, c_418])).
% 4.47/1.82  tff(c_428, plain, (![C_37]: (C_37='#skF_2'('#skF_5') | k1_funct_1('#skF_5', C_37)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | ~r2_hidden(C_37, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_92, c_427])).
% 4.47/1.82  tff(c_704, plain, (![C_37]: (C_37='#skF_2'('#skF_5') | k1_funct_1('#skF_5', C_37)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden(C_37, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_623, c_428])).
% 4.47/1.82  tff(c_707, plain, ('#skF_2'('#skF_5')='#skF_3'('#skF_5') | ~r2_hidden('#skF_3'('#skF_5'), '#skF_4')), inference(reflexivity, [status(thm), theory('equality')], [c_704])).
% 4.47/1.82  tff(c_709, plain, ('#skF_2'('#skF_5')='#skF_3'('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_617, c_707])).
% 4.47/1.82  tff(c_711, plain, $false, inference(negUnitSimplification, [status(thm)], [c_209, c_709])).
% 4.47/1.82  tff(c_712, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_580])).
% 4.47/1.82  tff(c_14, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.47/1.82  tff(c_736, plain, (![A_7]: (r1_tarski('#skF_4', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_712, c_14])).
% 4.47/1.82  tff(c_18, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.47/1.82  tff(c_735, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_712, c_712, c_18])).
% 4.47/1.82  tff(c_128, plain, (![A_50, B_51]: (r1_tarski(A_50, B_51) | ~m1_subset_1(A_50, k1_zfmisc_1(B_51)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.47/1.82  tff(c_136, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_60, c_128])).
% 4.47/1.82  tff(c_137, plain, (![B_52, A_53]: (B_52=A_53 | ~r1_tarski(B_52, A_53) | ~r1_tarski(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.47/1.82  tff(c_144, plain, (k2_zfmisc_1('#skF_4', '#skF_4')='#skF_5' | ~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_136, c_137])).
% 4.47/1.82  tff(c_201, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_144])).
% 4.47/1.82  tff(c_757, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_735, c_201])).
% 4.47/1.82  tff(c_762, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_736, c_757])).
% 4.47/1.82  tff(c_763, plain, (k2_zfmisc_1('#skF_4', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_144])).
% 4.47/1.82  tff(c_766, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_763, c_60])).
% 4.47/1.82  tff(c_838, plain, (![A_140, B_141, C_142]: (k1_relset_1(A_140, B_141, C_142)=k1_relat_1(C_142) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.47/1.82  tff(c_920, plain, (![C_155]: (k1_relset_1('#skF_4', '#skF_4', C_155)=k1_relat_1(C_155) | ~m1_subset_1(C_155, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_763, c_838])).
% 4.47/1.82  tff(c_928, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_766, c_920])).
% 4.47/1.82  tff(c_1098, plain, (![B_183, A_184, C_185]: (k1_xboole_0=B_183 | k1_relset_1(A_184, B_183, C_185)=A_184 | ~v1_funct_2(C_185, A_184, B_183) | ~m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1(A_184, B_183))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.47/1.82  tff(c_1101, plain, (![C_185]: (k1_xboole_0='#skF_4' | k1_relset_1('#skF_4', '#skF_4', C_185)='#skF_4' | ~v1_funct_2(C_185, '#skF_4', '#skF_4') | ~m1_subset_1(C_185, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_763, c_1098])).
% 4.47/1.82  tff(c_1114, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_1101])).
% 4.47/1.82  tff(c_16, plain, (![B_9, A_8]: (k1_xboole_0=B_9 | k1_xboole_0=A_8 | k2_zfmisc_1(A_8, B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.47/1.82  tff(c_771, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_4' | k1_xboole_0!='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_763, c_16])).
% 4.47/1.82  tff(c_813, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_771])).
% 4.47/1.82  tff(c_1143, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1114, c_813])).
% 4.47/1.82  tff(c_1150, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1114, c_1114, c_18])).
% 4.47/1.82  tff(c_1177, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1150, c_763])).
% 4.47/1.82  tff(c_1179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1143, c_1177])).
% 4.47/1.82  tff(c_1198, plain, (![C_193]: (k1_relset_1('#skF_4', '#skF_4', C_193)='#skF_4' | ~v1_funct_2(C_193, '#skF_4', '#skF_4') | ~m1_subset_1(C_193, k1_zfmisc_1('#skF_5')))), inference(splitRight, [status(thm)], [c_1101])).
% 4.47/1.82  tff(c_1201, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')='#skF_4' | ~v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_766, c_1198])).
% 4.47/1.82  tff(c_1208, plain, (k1_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_928, c_1201])).
% 4.47/1.82  tff(c_1220, plain, (r2_hidden('#skF_3'('#skF_5'), '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1208, c_36])).
% 4.47/1.82  tff(c_1234, plain, (r2_hidden('#skF_3'('#skF_5'), '#skF_4') | v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_64, c_1220])).
% 4.47/1.82  tff(c_1235, plain, (r2_hidden('#skF_3'('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_92, c_1234])).
% 4.47/1.82  tff(c_1226, plain, (r2_hidden('#skF_2'('#skF_5'), '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1208, c_38])).
% 4.47/1.82  tff(c_1240, plain, (r2_hidden('#skF_2'('#skF_5'), '#skF_4') | v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_64, c_1226])).
% 4.47/1.82  tff(c_1241, plain, (r2_hidden('#skF_2'('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_92, c_1240])).
% 4.47/1.82  tff(c_1029, plain, (![A_176]: (k1_funct_1(A_176, '#skF_2'(A_176))=k1_funct_1(A_176, '#skF_3'(A_176)) | v2_funct_1(A_176) | ~v1_funct_1(A_176) | ~v1_relat_1(A_176))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.47/1.82  tff(c_827, plain, (![D_38, C_37]: (D_38=C_37 | k1_funct_1('#skF_5', D_38)!=k1_funct_1('#skF_5', C_37) | ~r2_hidden(D_38, '#skF_4') | ~r2_hidden(C_37, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_92, c_84])).
% 4.47/1.82  tff(c_1035, plain, (![C_37]: (C_37='#skF_2'('#skF_5') | k1_funct_1('#skF_5', C_37)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | ~r2_hidden(C_37, '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1029, c_827])).
% 4.47/1.82  tff(c_1044, plain, (![C_37]: (C_37='#skF_2'('#skF_5') | k1_funct_1('#skF_5', C_37)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | ~r2_hidden(C_37, '#skF_4') | v2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_64, c_1035])).
% 4.47/1.82  tff(c_1045, plain, (![C_37]: (C_37='#skF_2'('#skF_5') | k1_funct_1('#skF_5', C_37)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | ~r2_hidden(C_37, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_92, c_1044])).
% 4.47/1.82  tff(c_1338, plain, (![C_37]: (C_37='#skF_2'('#skF_5') | k1_funct_1('#skF_5', C_37)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden(C_37, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1241, c_1045])).
% 4.47/1.82  tff(c_1341, plain, ('#skF_2'('#skF_5')='#skF_3'('#skF_5') | ~r2_hidden('#skF_3'('#skF_5'), '#skF_4')), inference(reflexivity, [status(thm), theory('equality')], [c_1338])).
% 4.47/1.82  tff(c_1343, plain, ('#skF_2'('#skF_5')='#skF_3'('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1235, c_1341])).
% 4.47/1.82  tff(c_1345, plain, $false, inference(negUnitSimplification, [status(thm)], [c_820, c_1343])).
% 4.47/1.82  tff(c_1347, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_771])).
% 4.47/1.82  tff(c_1346, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_771])).
% 4.47/1.82  tff(c_1382, plain, ('#skF_5'='#skF_4' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1347, c_1347, c_1346])).
% 4.47/1.82  tff(c_1383, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_1382])).
% 4.47/1.82  tff(c_1399, plain, (~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1383, c_92])).
% 4.47/1.82  tff(c_1397, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1383, c_173])).
% 4.47/1.82  tff(c_1400, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1383, c_64])).
% 4.47/1.82  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.47/1.82  tff(c_1356, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1347, c_6])).
% 4.47/1.82  tff(c_1393, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1383, c_1356])).
% 4.47/1.82  tff(c_1395, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1383, c_1383, c_766])).
% 4.47/1.82  tff(c_1355, plain, (![A_7]: (r1_tarski('#skF_5', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_1347, c_14])).
% 4.47/1.82  tff(c_1392, plain, (![A_7]: (r1_tarski('#skF_4', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_1383, c_1355])).
% 4.47/1.82  tff(c_24, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.47/1.82  tff(c_1519, plain, (![A_214, B_215, C_216]: (k1_relset_1(A_214, B_215, C_216)=k1_relat_1(C_216) | ~m1_subset_1(C_216, k1_zfmisc_1(k2_zfmisc_1(A_214, B_215))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.47/1.82  tff(c_1635, plain, (![A_235, B_236, A_237]: (k1_relset_1(A_235, B_236, A_237)=k1_relat_1(A_237) | ~r1_tarski(A_237, k2_zfmisc_1(A_235, B_236)))), inference(resolution, [status(thm)], [c_24, c_1519])).
% 4.47/1.82  tff(c_1650, plain, (![A_235, B_236]: (k1_relset_1(A_235, B_236, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1392, c_1635])).
% 4.47/1.82  tff(c_1398, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1383, c_62])).
% 4.47/1.82  tff(c_1394, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1383, c_1347])).
% 4.47/1.82  tff(c_20, plain, (![B_9]: (k2_zfmisc_1(k1_xboole_0, B_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.47/1.82  tff(c_56, plain, (![B_31, C_32]: (k1_relset_1(k1_xboole_0, B_31, C_32)=k1_xboole_0 | ~v1_funct_2(C_32, k1_xboole_0, B_31) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_31))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.47/1.82  tff(c_86, plain, (![B_31, C_32]: (k1_relset_1(k1_xboole_0, B_31, C_32)=k1_xboole_0 | ~v1_funct_2(C_32, k1_xboole_0, B_31) | ~m1_subset_1(C_32, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_56])).
% 4.47/1.82  tff(c_1680, plain, (![B_245, C_246]: (k1_relset_1('#skF_4', B_245, C_246)='#skF_4' | ~v1_funct_2(C_246, '#skF_4', B_245) | ~m1_subset_1(C_246, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1394, c_1394, c_1394, c_1394, c_86])).
% 4.47/1.82  tff(c_1685, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_4')='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_1398, c_1680])).
% 4.47/1.82  tff(c_1692, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1395, c_1650, c_1685])).
% 4.47/1.82  tff(c_1469, plain, (![A_211]: (r2_hidden('#skF_2'(A_211), k1_relat_1(A_211)) | v2_funct_1(A_211) | ~v1_funct_1(A_211) | ~v1_relat_1(A_211))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.47/1.82  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.47/1.82  tff(c_1473, plain, (![A_211]: (~v1_xboole_0(k1_relat_1(A_211)) | v2_funct_1(A_211) | ~v1_funct_1(A_211) | ~v1_relat_1(A_211))), inference(resolution, [status(thm)], [c_1469, c_2])).
% 4.47/1.82  tff(c_1707, plain, (~v1_xboole_0('#skF_4') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1692, c_1473])).
% 4.47/1.82  tff(c_1717, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1397, c_1400, c_1393, c_1707])).
% 4.47/1.82  tff(c_1719, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1399, c_1717])).
% 4.47/1.82  tff(c_1720, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_1382])).
% 4.47/1.82  tff(c_1721, plain, ('#skF_5'!='#skF_4'), inference(splitRight, [status(thm)], [c_1382])).
% 4.47/1.82  tff(c_1737, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1720, c_1721])).
% 4.47/1.82  tff(c_1739, plain, (v2_funct_1('#skF_5')), inference(splitRight, [status(thm)], [c_66])).
% 4.47/1.82  tff(c_72, plain, (r2_hidden('#skF_6', '#skF_4') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.47/1.82  tff(c_1769, plain, (r2_hidden('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1739, c_72])).
% 4.47/1.82  tff(c_1770, plain, (![B_253, A_254]: (~r2_hidden(B_253, A_254) | ~v1_xboole_0(A_254))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.47/1.82  tff(c_1774, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1769, c_1770])).
% 4.47/1.82  tff(c_1738, plain, ('#skF_7'!='#skF_6'), inference(splitRight, [status(thm)], [c_66])).
% 4.47/1.82  tff(c_1802, plain, (![B_260, A_261]: (v1_relat_1(B_260) | ~m1_subset_1(B_260, k1_zfmisc_1(A_261)) | ~v1_relat_1(A_261))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.47/1.82  tff(c_1808, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_60, c_1802])).
% 4.47/1.82  tff(c_1812, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1808])).
% 4.47/1.82  tff(c_70, plain, (r2_hidden('#skF_7', '#skF_4') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.47/1.82  tff(c_1776, plain, (r2_hidden('#skF_7', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1739, c_70])).
% 4.47/1.82  tff(c_1902, plain, (![A_274, B_275, C_276]: (k1_relset_1(A_274, B_275, C_276)=k1_relat_1(C_276) | ~m1_subset_1(C_276, k1_zfmisc_1(k2_zfmisc_1(A_274, B_275))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.47/1.82  tff(c_1917, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_1902])).
% 4.47/1.82  tff(c_2227, plain, (![B_321, A_322, C_323]: (k1_xboole_0=B_321 | k1_relset_1(A_322, B_321, C_323)=A_322 | ~v1_funct_2(C_323, A_322, B_321) | ~m1_subset_1(C_323, k1_zfmisc_1(k2_zfmisc_1(A_322, B_321))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.47/1.82  tff(c_2234, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_4', '#skF_4', '#skF_5')='#skF_4' | ~v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_60, c_2227])).
% 4.47/1.82  tff(c_2244, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1917, c_2234])).
% 4.47/1.82  tff(c_2246, plain, (k1_relat_1('#skF_5')='#skF_4'), inference(splitLeft, [status(thm)], [c_2244])).
% 4.47/1.82  tff(c_68, plain, (k1_funct_1('#skF_5', '#skF_7')=k1_funct_1('#skF_5', '#skF_6') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.47/1.82  tff(c_1797, plain, (k1_funct_1('#skF_5', '#skF_7')=k1_funct_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1739, c_68])).
% 4.47/1.82  tff(c_2333, plain, (![C_330, B_331, A_332]: (C_330=B_331 | k1_funct_1(A_332, C_330)!=k1_funct_1(A_332, B_331) | ~r2_hidden(C_330, k1_relat_1(A_332)) | ~r2_hidden(B_331, k1_relat_1(A_332)) | ~v2_funct_1(A_332) | ~v1_funct_1(A_332) | ~v1_relat_1(A_332))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.47/1.82  tff(c_2341, plain, (![C_330]: (C_330='#skF_7' | k1_funct_1('#skF_5', C_330)!=k1_funct_1('#skF_5', '#skF_6') | ~r2_hidden(C_330, k1_relat_1('#skF_5')) | ~r2_hidden('#skF_7', k1_relat_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1797, c_2333])).
% 4.47/1.82  tff(c_2362, plain, (![C_335]: (C_335='#skF_7' | k1_funct_1('#skF_5', C_335)!=k1_funct_1('#skF_5', '#skF_6') | ~r2_hidden(C_335, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1812, c_64, c_1739, c_1776, c_2246, c_2246, c_2341])).
% 4.47/1.82  tff(c_2376, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_1769, c_2362])).
% 4.47/1.82  tff(c_2388, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1738, c_2376])).
% 4.47/1.82  tff(c_2389, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_2244])).
% 4.47/1.82  tff(c_2410, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2389, c_6])).
% 4.47/1.82  tff(c_2412, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1774, c_2410])).
% 4.47/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.47/1.82  
% 4.47/1.82  Inference rules
% 4.47/1.82  ----------------------
% 4.47/1.82  #Ref     : 8
% 4.47/1.82  #Sup     : 448
% 4.47/1.82  #Fact    : 0
% 4.47/1.82  #Define  : 0
% 4.47/1.82  #Split   : 24
% 4.47/1.82  #Chain   : 0
% 4.47/1.82  #Close   : 0
% 4.47/1.82  
% 4.47/1.82  Ordering : KBO
% 4.47/1.82  
% 4.47/1.82  Simplification rules
% 4.47/1.82  ----------------------
% 4.47/1.82  #Subsume      : 75
% 4.47/1.82  #Demod        : 563
% 4.47/1.82  #Tautology    : 263
% 4.47/1.82  #SimpNegUnit  : 31
% 4.47/1.82  #BackRed      : 130
% 4.47/1.82  
% 4.47/1.82  #Partial instantiations: 0
% 4.47/1.82  #Strategies tried      : 1
% 4.47/1.82  
% 4.47/1.82  Timing (in seconds)
% 4.47/1.82  ----------------------
% 4.47/1.82  Preprocessing        : 0.36
% 4.47/1.82  Parsing              : 0.18
% 4.47/1.82  CNF conversion       : 0.03
% 4.47/1.82  Main loop            : 0.61
% 4.47/1.82  Inferencing          : 0.21
% 4.47/1.82  Reduction            : 0.20
% 4.47/1.82  Demodulation         : 0.13
% 4.47/1.82  BG Simplification    : 0.03
% 4.47/1.82  Subsumption          : 0.11
% 4.47/1.82  Abstraction          : 0.03
% 4.47/1.82  MUC search           : 0.00
% 4.47/1.82  Cooper               : 0.00
% 4.47/1.82  Total                : 1.03
% 4.47/1.82  Index Insertion      : 0.00
% 4.47/1.82  Index Deletion       : 0.00
% 4.47/1.82  Index Matching       : 0.00
% 4.47/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
