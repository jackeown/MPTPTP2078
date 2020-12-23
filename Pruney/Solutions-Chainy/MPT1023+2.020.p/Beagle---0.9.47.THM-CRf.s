%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:19 EST 2020

% Result     : Theorem 11.84s
% Output     : CNFRefutation 12.09s
% Verified   : 
% Statistics : Number of formulae       :  195 (1364 expanded)
%              Number of leaves         :   35 ( 453 expanded)
%              Depth                    :   17
%              Number of atoms          :  401 (4143 expanded)
%              Number of equality atoms :  154 (1113 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_135,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_funct_2)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ! [D] :
          ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( r2_relset_1(A,B,C,D)
          <=> ! [E] :
                ( m1_subset_1(E,A)
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ( r2_hidden(k4_tarski(E,F),C)
                    <=> r2_hidden(k4_tarski(E,F),D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_114,axiom,(
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

tff(f_71,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_156,plain,(
    ! [C_76,A_77,B_78] :
      ( v1_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_177,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_156])).

tff(c_68,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_66,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_70,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_654,plain,(
    ! [A_146,B_147,C_148,D_149] :
      ( m1_subset_1('#skF_3'(A_146,B_147,C_148,D_149),B_147)
      | r2_relset_1(A_146,B_147,C_148,D_149)
      | ~ m1_subset_1(D_149,k1_zfmisc_1(k2_zfmisc_1(A_146,B_147)))
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_146,B_147))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_764,plain,(
    ! [C_157] :
      ( m1_subset_1('#skF_3'('#skF_4','#skF_5',C_157,'#skF_6'),'#skF_5')
      | r2_relset_1('#skF_4','#skF_5',C_157,'#skF_6')
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_70,c_654])).

tff(c_780,plain,
    ( m1_subset_1('#skF_3'('#skF_4','#skF_5','#skF_6','#skF_6'),'#skF_5')
    | r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_764])).

tff(c_783,plain,(
    r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_780])).

tff(c_266,plain,(
    ! [A_95,B_96,C_97] :
      ( k1_relset_1(A_95,B_96,C_97) = k1_relat_1(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_289,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_266])).

tff(c_463,plain,(
    ! [B_127,A_128,C_129] :
      ( k1_xboole_0 = B_127
      | k1_relset_1(A_128,B_127,C_129) = A_128
      | ~ v1_funct_2(C_129,A_128,B_127)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_128,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_473,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_463])).

tff(c_490,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_289,c_473])).

tff(c_500,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_490])).

tff(c_176,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_156])).

tff(c_74,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_72,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_288,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_266])).

tff(c_470,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_463])).

tff(c_487,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_288,c_470])).

tff(c_494,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_487])).

tff(c_525,plain,(
    ! [A_132,B_133] :
      ( r2_hidden('#skF_1'(A_132,B_133),k1_relat_1(A_132))
      | B_133 = A_132
      | k1_relat_1(B_133) != k1_relat_1(A_132)
      | ~ v1_funct_1(B_133)
      | ~ v1_relat_1(B_133)
      | ~ v1_funct_1(A_132)
      | ~ v1_relat_1(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_536,plain,(
    ! [B_133] :
      ( r2_hidden('#skF_1'('#skF_6',B_133),'#skF_4')
      | B_133 = '#skF_6'
      | k1_relat_1(B_133) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_133)
      | ~ v1_relat_1(B_133)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_525])).

tff(c_567,plain,(
    ! [B_137] :
      ( r2_hidden('#skF_1'('#skF_6',B_137),'#skF_4')
      | B_137 = '#skF_6'
      | k1_relat_1(B_137) != '#skF_4'
      | ~ v1_funct_1(B_137)
      | ~ v1_relat_1(B_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_74,c_494,c_536])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_580,plain,(
    ! [B_139] :
      ( m1_subset_1('#skF_1'('#skF_6',B_139),'#skF_4')
      | B_139 = '#skF_6'
      | k1_relat_1(B_139) != '#skF_4'
      | ~ v1_funct_1(B_139)
      | ~ v1_relat_1(B_139) ) ),
    inference(resolution,[status(thm)],[c_567,c_16])).

tff(c_62,plain,(
    ! [E_59] :
      ( k1_funct_1('#skF_7',E_59) = k1_funct_1('#skF_6',E_59)
      | ~ m1_subset_1(E_59,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1532,plain,(
    ! [B_212] :
      ( k1_funct_1('#skF_7','#skF_1'('#skF_6',B_212)) = k1_funct_1('#skF_6','#skF_1'('#skF_6',B_212))
      | B_212 = '#skF_6'
      | k1_relat_1(B_212) != '#skF_4'
      | ~ v1_funct_1(B_212)
      | ~ v1_relat_1(B_212) ) ),
    inference(resolution,[status(thm)],[c_580,c_62])).

tff(c_24,plain,(
    ! [B_17,A_13] :
      ( k1_funct_1(B_17,'#skF_1'(A_13,B_17)) != k1_funct_1(A_13,'#skF_1'(A_13,B_17))
      | B_17 = A_13
      | k1_relat_1(B_17) != k1_relat_1(A_13)
      | ~ v1_funct_1(B_17)
      | ~ v1_relat_1(B_17)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1539,plain,
    ( k1_relat_1('#skF_7') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_7' = '#skF_6'
    | k1_relat_1('#skF_7') != '#skF_4'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1532,c_24])).

tff(c_1546,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_68,c_500,c_176,c_74,c_500,c_494,c_1539])).

tff(c_60,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1573,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1546,c_60])).

tff(c_1588,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_783,c_1573])).

tff(c_1590,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(splitRight,[status(thm)],[c_780])).

tff(c_40,plain,(
    ! [A_22,B_23,C_24,D_38] :
      ( r2_hidden(k4_tarski('#skF_2'(A_22,B_23,C_24,D_38),'#skF_3'(A_22,B_23,C_24,D_38)),C_24)
      | r2_hidden(k4_tarski('#skF_2'(A_22,B_23,C_24,D_38),'#skF_3'(A_22,B_23,C_24,D_38)),D_38)
      | r2_relset_1(A_22,B_23,C_24,D_38)
      | ~ m1_subset_1(D_38,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_6389,plain,(
    ! [A_22,B_23,D_38] :
      ( r2_relset_1(A_22,B_23,D_38,D_38)
      | ~ m1_subset_1(D_38,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | r2_hidden(k4_tarski('#skF_2'(A_22,B_23,D_38,D_38),'#skF_3'(A_22,B_23,D_38,D_38)),D_38) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_40])).

tff(c_8562,plain,(
    ! [A_658,B_659,D_660] :
      ( r2_relset_1(A_658,B_659,D_660,D_660)
      | ~ m1_subset_1(D_660,k1_zfmisc_1(k2_zfmisc_1(A_658,B_659)))
      | r2_hidden(k4_tarski('#skF_2'(A_658,B_659,D_660,D_660),'#skF_3'(A_658,B_659,D_660,D_660)),D_660) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_40])).

tff(c_34,plain,(
    ! [A_22,B_23,C_24,D_38] :
      ( ~ r2_hidden(k4_tarski('#skF_2'(A_22,B_23,C_24,D_38),'#skF_3'(A_22,B_23,C_24,D_38)),D_38)
      | ~ r2_hidden(k4_tarski('#skF_2'(A_22,B_23,C_24,D_38),'#skF_3'(A_22,B_23,C_24,D_38)),C_24)
      | r2_relset_1(A_22,B_23,C_24,D_38)
      | ~ m1_subset_1(D_38,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_11245,plain,(
    ! [A_841,B_842,D_843] :
      ( ~ r2_hidden(k4_tarski('#skF_2'(A_841,B_842,D_843,D_843),'#skF_3'(A_841,B_842,D_843,D_843)),D_843)
      | r2_relset_1(A_841,B_842,D_843,D_843)
      | ~ m1_subset_1(D_843,k1_zfmisc_1(k2_zfmisc_1(A_841,B_842))) ) ),
    inference(resolution,[status(thm)],[c_8562,c_34])).

tff(c_11264,plain,(
    ! [A_844,B_845,D_846] :
      ( r2_relset_1(A_844,B_845,D_846,D_846)
      | ~ m1_subset_1(D_846,k1_zfmisc_1(k2_zfmisc_1(A_844,B_845))) ) ),
    inference(resolution,[status(thm)],[c_6389,c_11245])).

tff(c_11335,plain,(
    r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_11264])).

tff(c_11367,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1590,c_11335])).

tff(c_11368,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_490])).

tff(c_14,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_108,plain,(
    ! [A_69,B_70] :
      ( r1_tarski(A_69,B_70)
      | ~ m1_subset_1(A_69,k1_zfmisc_1(B_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_124,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(resolution,[status(thm)],[c_14,c_108])).

tff(c_11387,plain,(
    ! [A_5] : r1_tarski('#skF_5',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11368,c_124])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_11390,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11368,c_11368,c_10])).

tff(c_123,plain,(
    r1_tarski('#skF_7',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_64,c_108])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_138,plain,
    ( k2_zfmisc_1('#skF_4','#skF_5') = '#skF_7'
    | ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_123,c_2])).

tff(c_249,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_11461,plain,(
    ~ r1_tarski('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11390,c_249])).

tff(c_11469,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11387,c_11461])).

tff(c_11470,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_487])).

tff(c_11497,plain,(
    ! [A_5] : r1_tarski('#skF_5',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11470,c_124])).

tff(c_11500,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11470,c_11470,c_10])).

tff(c_11544,plain,(
    ~ r1_tarski('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11500,c_249])).

tff(c_11552,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11497,c_11544])).

tff(c_11553,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_11559,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11553,c_64])).

tff(c_11644,plain,(
    ! [A_862,B_863,C_864] :
      ( k1_relset_1(A_862,B_863,C_864) = k1_relat_1(C_864)
      | ~ m1_subset_1(C_864,k1_zfmisc_1(k2_zfmisc_1(A_862,B_863))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_11672,plain,(
    ! [C_867] :
      ( k1_relset_1('#skF_4','#skF_5',C_867) = k1_relat_1(C_867)
      | ~ m1_subset_1(C_867,k1_zfmisc_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11553,c_11644])).

tff(c_11688,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_11559,c_11672])).

tff(c_11768,plain,(
    ! [B_882,C_883,A_884] :
      ( k1_xboole_0 = B_882
      | v1_funct_2(C_883,A_884,B_882)
      | k1_relset_1(A_884,B_882,C_883) != A_884
      | ~ m1_subset_1(C_883,k1_zfmisc_1(k2_zfmisc_1(A_884,B_882))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_11771,plain,(
    ! [C_883] :
      ( k1_xboole_0 = '#skF_5'
      | v1_funct_2(C_883,'#skF_4','#skF_5')
      | k1_relset_1('#skF_4','#skF_5',C_883) != '#skF_4'
      | ~ m1_subset_1(C_883,k1_zfmisc_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11553,c_11768])).

tff(c_11898,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_11771])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_11568,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 != '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_11553,c_8])).

tff(c_11671,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_11568])).

tff(c_11911,plain,(
    '#skF_7' != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11898,c_11671])).

tff(c_11922,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11898,c_11898,c_10])).

tff(c_12017,plain,(
    '#skF_7' = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11922,c_11553])).

tff(c_12019,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11911,c_12017])).

tff(c_12021,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_11771])).

tff(c_11865,plain,(
    ! [B_896,A_897,C_898] :
      ( k1_xboole_0 = B_896
      | k1_relset_1(A_897,B_896,C_898) = A_897
      | ~ v1_funct_2(C_898,A_897,B_896)
      | ~ m1_subset_1(C_898,k1_zfmisc_1(k2_zfmisc_1(A_897,B_896))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_11868,plain,(
    ! [C_898] :
      ( k1_xboole_0 = '#skF_5'
      | k1_relset_1('#skF_4','#skF_5',C_898) = '#skF_4'
      | ~ v1_funct_2(C_898,'#skF_4','#skF_5')
      | ~ m1_subset_1(C_898,k1_zfmisc_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11553,c_11865])).

tff(c_12022,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_11868])).

tff(c_12023,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12021,c_12022])).

tff(c_12050,plain,(
    ! [C_910] :
      ( k1_relset_1('#skF_4','#skF_5',C_910) = '#skF_4'
      | ~ v1_funct_2(C_910,'#skF_4','#skF_5')
      | ~ m1_subset_1(C_910,k1_zfmisc_1('#skF_7')) ) ),
    inference(splitRight,[status(thm)],[c_11868])).

tff(c_12056,plain,
    ( k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_11559,c_12050])).

tff(c_12070,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_11688,c_12056])).

tff(c_11558,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11553,c_70])).

tff(c_11687,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_11558,c_11672])).

tff(c_12053,plain,
    ( k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_11558,c_12050])).

tff(c_12067,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_11687,c_12053])).

tff(c_26,plain,(
    ! [A_13,B_17] :
      ( r2_hidden('#skF_1'(A_13,B_17),k1_relat_1(A_13))
      | B_17 = A_13
      | k1_relat_1(B_17) != k1_relat_1(A_13)
      | ~ v1_funct_1(B_17)
      | ~ v1_relat_1(B_17)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_12078,plain,(
    ! [B_17] :
      ( r2_hidden('#skF_1'('#skF_6',B_17),'#skF_4')
      | B_17 = '#skF_6'
      | k1_relat_1(B_17) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_17)
      | ~ v1_relat_1(B_17)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12067,c_26])).

tff(c_12180,plain,(
    ! [B_916] :
      ( r2_hidden('#skF_1'('#skF_6',B_916),'#skF_4')
      | B_916 = '#skF_6'
      | k1_relat_1(B_916) != '#skF_4'
      | ~ v1_funct_1(B_916)
      | ~ v1_relat_1(B_916) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_74,c_12067,c_12078])).

tff(c_12196,plain,(
    ! [B_918] :
      ( m1_subset_1('#skF_1'('#skF_6',B_918),'#skF_4')
      | B_918 = '#skF_6'
      | k1_relat_1(B_918) != '#skF_4'
      | ~ v1_funct_1(B_918)
      | ~ v1_relat_1(B_918) ) ),
    inference(resolution,[status(thm)],[c_12180,c_16])).

tff(c_12364,plain,(
    ! [B_935] :
      ( k1_funct_1('#skF_7','#skF_1'('#skF_6',B_935)) = k1_funct_1('#skF_6','#skF_1'('#skF_6',B_935))
      | B_935 = '#skF_6'
      | k1_relat_1(B_935) != '#skF_4'
      | ~ v1_funct_1(B_935)
      | ~ v1_relat_1(B_935) ) ),
    inference(resolution,[status(thm)],[c_12196,c_62])).

tff(c_12371,plain,
    ( k1_relat_1('#skF_7') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_7' = '#skF_6'
    | k1_relat_1('#skF_7') != '#skF_4'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_12364,c_24])).

tff(c_12378,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_68,c_12070,c_176,c_74,c_12070,c_12067,c_12371])).

tff(c_122,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_70,c_108])).

tff(c_141,plain,
    ( k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6'
    | ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_122,c_2])).

tff(c_215,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_141])).

tff(c_11555,plain,(
    ~ r1_tarski('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11553,c_215])).

tff(c_12397,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12378,c_11555])).

tff(c_12409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_12397])).

tff(c_12411,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_11568])).

tff(c_12419,plain,(
    ! [A_5] : r1_tarski('#skF_7',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12411,c_124])).

tff(c_12431,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12419,c_11555])).

tff(c_12432,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_141])).

tff(c_12437,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12432,c_64])).

tff(c_12479,plain,(
    ! [A_942,B_943,C_944] :
      ( k1_relset_1(A_942,B_943,C_944) = k1_relat_1(C_944)
      | ~ m1_subset_1(C_944,k1_zfmisc_1(k2_zfmisc_1(A_942,B_943))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_12625,plain,(
    ! [C_967] :
      ( k1_relset_1('#skF_4','#skF_5',C_967) = k1_relat_1(C_967)
      | ~ m1_subset_1(C_967,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12432,c_12479])).

tff(c_12640,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_12437,c_12625])).

tff(c_12740,plain,(
    ! [B_980,C_981,A_982] :
      ( k1_xboole_0 = B_980
      | v1_funct_2(C_981,A_982,B_980)
      | k1_relset_1(A_982,B_980,C_981) != A_982
      | ~ m1_subset_1(C_981,k1_zfmisc_1(k2_zfmisc_1(A_982,B_980))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_12743,plain,(
    ! [C_981] :
      ( k1_xboole_0 = '#skF_5'
      | v1_funct_2(C_981,'#skF_4','#skF_5')
      | k1_relset_1('#skF_4','#skF_5',C_981) != '#skF_4'
      | ~ m1_subset_1(C_981,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12432,c_12740])).

tff(c_12778,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_12743])).

tff(c_12442,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 != '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_12432,c_8])).

tff(c_12478,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_12442])).

tff(c_12791,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12778,c_12478])).

tff(c_12884,plain,(
    ! [A_990] : k2_zfmisc_1(A_990,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12778,c_12778,c_10])).

tff(c_12904,plain,(
    '#skF_5' = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_12884,c_12432])).

tff(c_12916,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12791,c_12904])).

tff(c_12918,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_12743])).

tff(c_12942,plain,(
    ! [B_992,A_993,C_994] :
      ( k1_xboole_0 = B_992
      | k1_relset_1(A_993,B_992,C_994) = A_993
      | ~ v1_funct_2(C_994,A_993,B_992)
      | ~ m1_subset_1(C_994,k1_zfmisc_1(k2_zfmisc_1(A_993,B_992))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_12945,plain,(
    ! [C_994] :
      ( k1_xboole_0 = '#skF_5'
      | k1_relset_1('#skF_4','#skF_5',C_994) = '#skF_4'
      | ~ v1_funct_2(C_994,'#skF_4','#skF_5')
      | ~ m1_subset_1(C_994,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12432,c_12942])).

tff(c_12992,plain,(
    ! [C_998] :
      ( k1_relset_1('#skF_4','#skF_5',C_998) = '#skF_4'
      | ~ v1_funct_2(C_998,'#skF_4','#skF_5')
      | ~ m1_subset_1(C_998,k1_zfmisc_1('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12918,c_12945])).

tff(c_12995,plain,
    ( k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_12437,c_12992])).

tff(c_13009,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_12640,c_12995])).

tff(c_12436,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12432,c_70])).

tff(c_12641,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_12436,c_12625])).

tff(c_12998,plain,
    ( k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_12436,c_12992])).

tff(c_13012,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_12641,c_12998])).

tff(c_13071,plain,(
    ! [A_1000,B_1001] :
      ( r2_hidden('#skF_1'(A_1000,B_1001),k1_relat_1(A_1000))
      | B_1001 = A_1000
      | k1_relat_1(B_1001) != k1_relat_1(A_1000)
      | ~ v1_funct_1(B_1001)
      | ~ v1_relat_1(B_1001)
      | ~ v1_funct_1(A_1000)
      | ~ v1_relat_1(A_1000) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_13079,plain,(
    ! [B_1001] :
      ( r2_hidden('#skF_1'('#skF_6',B_1001),'#skF_4')
      | B_1001 = '#skF_6'
      | k1_relat_1(B_1001) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_1001)
      | ~ v1_relat_1(B_1001)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13012,c_13071])).

tff(c_13089,plain,(
    ! [B_1002] :
      ( r2_hidden('#skF_1'('#skF_6',B_1002),'#skF_4')
      | B_1002 = '#skF_6'
      | k1_relat_1(B_1002) != '#skF_4'
      | ~ v1_funct_1(B_1002)
      | ~ v1_relat_1(B_1002) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_74,c_13012,c_13079])).

tff(c_13105,plain,(
    ! [B_1004] :
      ( m1_subset_1('#skF_1'('#skF_6',B_1004),'#skF_4')
      | B_1004 = '#skF_6'
      | k1_relat_1(B_1004) != '#skF_4'
      | ~ v1_funct_1(B_1004)
      | ~ v1_relat_1(B_1004) ) ),
    inference(resolution,[status(thm)],[c_13089,c_16])).

tff(c_13109,plain,(
    ! [B_1004] :
      ( k1_funct_1('#skF_7','#skF_1'('#skF_6',B_1004)) = k1_funct_1('#skF_6','#skF_1'('#skF_6',B_1004))
      | B_1004 = '#skF_6'
      | k1_relat_1(B_1004) != '#skF_4'
      | ~ v1_funct_1(B_1004)
      | ~ v1_relat_1(B_1004) ) ),
    inference(resolution,[status(thm)],[c_13105,c_62])).

tff(c_13484,plain,(
    ! [B_1029,A_1030] :
      ( k1_funct_1(B_1029,'#skF_1'(A_1030,B_1029)) != k1_funct_1(A_1030,'#skF_1'(A_1030,B_1029))
      | B_1029 = A_1030
      | k1_relat_1(B_1029) != k1_relat_1(A_1030)
      | ~ v1_funct_1(B_1029)
      | ~ v1_relat_1(B_1029)
      | ~ v1_funct_1(A_1030)
      | ~ v1_relat_1(A_1030) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_13491,plain,
    ( k1_relat_1('#skF_7') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_7' = '#skF_6'
    | k1_relat_1('#skF_7') != '#skF_4'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_13109,c_13484])).

tff(c_13496,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_68,c_13009,c_176,c_74,c_13012,c_13009,c_13491])).

tff(c_12435,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12432,c_123])).

tff(c_12450,plain,
    ( '#skF_7' = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_12435,c_2])).

tff(c_12476,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_12450])).

tff(c_13504,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13496,c_12476])).

tff(c_13517,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_13504])).

tff(c_13519,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_12442])).

tff(c_13526,plain,(
    ! [A_5] : r1_tarski('#skF_6',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13519,c_124])).

tff(c_13538,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13526,c_12476])).

tff(c_13539,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_12450])).

tff(c_13541,plain,
    ( '#skF_7' = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12432,c_12432,c_138])).

tff(c_13542,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_13541])).

tff(c_13561,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_13539,c_13542])).

tff(c_13562,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_13541])).

tff(c_13569,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13562,c_60])).

tff(c_15085,plain,(
    ! [A_22,B_23,C_24] :
      ( r2_relset_1(A_22,B_23,C_24,C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | r2_hidden(k4_tarski('#skF_2'(A_22,B_23,C_24,C_24),'#skF_3'(A_22,B_23,C_24,C_24)),C_24) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_40])).

tff(c_16607,plain,(
    ! [A_1286,B_1287,C_1288] :
      ( r2_relset_1(A_1286,B_1287,C_1288,C_1288)
      | ~ m1_subset_1(C_1288,k1_zfmisc_1(k2_zfmisc_1(A_1286,B_1287)))
      | r2_hidden(k4_tarski('#skF_2'(A_1286,B_1287,C_1288,C_1288),'#skF_3'(A_1286,B_1287,C_1288,C_1288)),C_1288) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_40])).

tff(c_19849,plain,(
    ! [A_1520,B_1521,C_1522] :
      ( ~ r2_hidden(k4_tarski('#skF_2'(A_1520,B_1521,C_1522,C_1522),'#skF_3'(A_1520,B_1521,C_1522,C_1522)),C_1522)
      | r2_relset_1(A_1520,B_1521,C_1522,C_1522)
      | ~ m1_subset_1(C_1522,k1_zfmisc_1(k2_zfmisc_1(A_1520,B_1521))) ) ),
    inference(resolution,[status(thm)],[c_16607,c_34])).

tff(c_19868,plain,(
    ! [A_1523,B_1524,C_1525] :
      ( r2_relset_1(A_1523,B_1524,C_1525,C_1525)
      | ~ m1_subset_1(C_1525,k1_zfmisc_1(k2_zfmisc_1(A_1523,B_1524))) ) ),
    inference(resolution,[status(thm)],[c_15085,c_19849])).

tff(c_19968,plain,(
    ! [C_1526] :
      ( r2_relset_1('#skF_4','#skF_5',C_1526,C_1526)
      | ~ m1_subset_1(C_1526,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12432,c_19868])).

tff(c_20036,plain,(
    r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_12436,c_19968])).

tff(c_20066,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13569,c_20036])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:49:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.84/4.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.90/4.61  
% 11.90/4.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.90/4.61  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 11.90/4.61  
% 11.90/4.61  %Foreground sorts:
% 11.90/4.61  
% 11.90/4.61  
% 11.90/4.61  %Background operators:
% 11.90/4.61  
% 11.90/4.61  
% 11.90/4.61  %Foreground operators:
% 11.90/4.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.90/4.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.90/4.61  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 11.90/4.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.90/4.61  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 11.90/4.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.90/4.61  tff('#skF_7', type, '#skF_7': $i).
% 11.90/4.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.90/4.61  tff('#skF_5', type, '#skF_5': $i).
% 11.90/4.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.90/4.61  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 11.90/4.61  tff('#skF_6', type, '#skF_6': $i).
% 11.90/4.61  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.90/4.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.90/4.61  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 11.90/4.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.90/4.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.90/4.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.90/4.61  tff('#skF_4', type, '#skF_4': $i).
% 11.90/4.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.90/4.61  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 11.90/4.61  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.90/4.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.90/4.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.90/4.61  
% 12.09/4.64  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.09/4.64  tff(f_135, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_funct_2)).
% 12.09/4.64  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 12.09/4.64  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, C, D) <=> (![E]: (m1_subset_1(E, A) => (![F]: (m1_subset_1(F, B) => (r2_hidden(k4_tarski(E, F), C) <=> r2_hidden(k4_tarski(E, F), D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relset_1)).
% 12.09/4.64  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 12.09/4.64  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 12.09/4.64  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 12.09/4.64  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 12.09/4.64  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 12.09/4.64  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 12.09/4.64  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 12.09/4.64  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.09/4.64  tff(c_64, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 12.09/4.64  tff(c_156, plain, (![C_76, A_77, B_78]: (v1_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.09/4.64  tff(c_177, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_64, c_156])).
% 12.09/4.64  tff(c_68, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_135])).
% 12.09/4.64  tff(c_66, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_135])).
% 12.09/4.64  tff(c_70, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 12.09/4.64  tff(c_654, plain, (![A_146, B_147, C_148, D_149]: (m1_subset_1('#skF_3'(A_146, B_147, C_148, D_149), B_147) | r2_relset_1(A_146, B_147, C_148, D_149) | ~m1_subset_1(D_149, k1_zfmisc_1(k2_zfmisc_1(A_146, B_147))) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_146, B_147))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 12.09/4.64  tff(c_764, plain, (![C_157]: (m1_subset_1('#skF_3'('#skF_4', '#skF_5', C_157, '#skF_6'), '#skF_5') | r2_relset_1('#skF_4', '#skF_5', C_157, '#skF_6') | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))))), inference(resolution, [status(thm)], [c_70, c_654])).
% 12.09/4.64  tff(c_780, plain, (m1_subset_1('#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_6'), '#skF_5') | r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_70, c_764])).
% 12.09/4.64  tff(c_783, plain, (r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(splitLeft, [status(thm)], [c_780])).
% 12.09/4.64  tff(c_266, plain, (![A_95, B_96, C_97]: (k1_relset_1(A_95, B_96, C_97)=k1_relat_1(C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 12.09/4.64  tff(c_289, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_64, c_266])).
% 12.09/4.64  tff(c_463, plain, (![B_127, A_128, C_129]: (k1_xboole_0=B_127 | k1_relset_1(A_128, B_127, C_129)=A_128 | ~v1_funct_2(C_129, A_128, B_127) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(A_128, B_127))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 12.09/4.64  tff(c_473, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_64, c_463])).
% 12.09/4.64  tff(c_490, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_289, c_473])).
% 12.09/4.64  tff(c_500, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(splitLeft, [status(thm)], [c_490])).
% 12.09/4.64  tff(c_176, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_70, c_156])).
% 12.09/4.64  tff(c_74, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_135])).
% 12.09/4.64  tff(c_72, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_135])).
% 12.09/4.64  tff(c_288, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_70, c_266])).
% 12.09/4.64  tff(c_470, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_70, c_463])).
% 12.09/4.64  tff(c_487, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_288, c_470])).
% 12.09/4.64  tff(c_494, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_487])).
% 12.09/4.64  tff(c_525, plain, (![A_132, B_133]: (r2_hidden('#skF_1'(A_132, B_133), k1_relat_1(A_132)) | B_133=A_132 | k1_relat_1(B_133)!=k1_relat_1(A_132) | ~v1_funct_1(B_133) | ~v1_relat_1(B_133) | ~v1_funct_1(A_132) | ~v1_relat_1(A_132))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.09/4.64  tff(c_536, plain, (![B_133]: (r2_hidden('#skF_1'('#skF_6', B_133), '#skF_4') | B_133='#skF_6' | k1_relat_1(B_133)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_133) | ~v1_relat_1(B_133) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_494, c_525])).
% 12.09/4.64  tff(c_567, plain, (![B_137]: (r2_hidden('#skF_1'('#skF_6', B_137), '#skF_4') | B_137='#skF_6' | k1_relat_1(B_137)!='#skF_4' | ~v1_funct_1(B_137) | ~v1_relat_1(B_137))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_74, c_494, c_536])).
% 12.09/4.64  tff(c_16, plain, (![A_6, B_7]: (m1_subset_1(A_6, B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.09/4.64  tff(c_580, plain, (![B_139]: (m1_subset_1('#skF_1'('#skF_6', B_139), '#skF_4') | B_139='#skF_6' | k1_relat_1(B_139)!='#skF_4' | ~v1_funct_1(B_139) | ~v1_relat_1(B_139))), inference(resolution, [status(thm)], [c_567, c_16])).
% 12.09/4.64  tff(c_62, plain, (![E_59]: (k1_funct_1('#skF_7', E_59)=k1_funct_1('#skF_6', E_59) | ~m1_subset_1(E_59, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_135])).
% 12.09/4.64  tff(c_1532, plain, (![B_212]: (k1_funct_1('#skF_7', '#skF_1'('#skF_6', B_212))=k1_funct_1('#skF_6', '#skF_1'('#skF_6', B_212)) | B_212='#skF_6' | k1_relat_1(B_212)!='#skF_4' | ~v1_funct_1(B_212) | ~v1_relat_1(B_212))), inference(resolution, [status(thm)], [c_580, c_62])).
% 12.09/4.64  tff(c_24, plain, (![B_17, A_13]: (k1_funct_1(B_17, '#skF_1'(A_13, B_17))!=k1_funct_1(A_13, '#skF_1'(A_13, B_17)) | B_17=A_13 | k1_relat_1(B_17)!=k1_relat_1(A_13) | ~v1_funct_1(B_17) | ~v1_relat_1(B_17) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.09/4.64  tff(c_1539, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_7'='#skF_6' | k1_relat_1('#skF_7')!='#skF_4' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1532, c_24])).
% 12.09/4.64  tff(c_1546, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_177, c_68, c_500, c_176, c_74, c_500, c_494, c_1539])).
% 12.09/4.64  tff(c_60, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_135])).
% 12.09/4.64  tff(c_1573, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1546, c_60])).
% 12.09/4.64  tff(c_1588, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_783, c_1573])).
% 12.09/4.64  tff(c_1590, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(splitRight, [status(thm)], [c_780])).
% 12.09/4.64  tff(c_40, plain, (![A_22, B_23, C_24, D_38]: (r2_hidden(k4_tarski('#skF_2'(A_22, B_23, C_24, D_38), '#skF_3'(A_22, B_23, C_24, D_38)), C_24) | r2_hidden(k4_tarski('#skF_2'(A_22, B_23, C_24, D_38), '#skF_3'(A_22, B_23, C_24, D_38)), D_38) | r2_relset_1(A_22, B_23, C_24, D_38) | ~m1_subset_1(D_38, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 12.09/4.64  tff(c_6389, plain, (![A_22, B_23, D_38]: (r2_relset_1(A_22, B_23, D_38, D_38) | ~m1_subset_1(D_38, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | r2_hidden(k4_tarski('#skF_2'(A_22, B_23, D_38, D_38), '#skF_3'(A_22, B_23, D_38, D_38)), D_38))), inference(factorization, [status(thm), theory('equality')], [c_40])).
% 12.09/4.64  tff(c_8562, plain, (![A_658, B_659, D_660]: (r2_relset_1(A_658, B_659, D_660, D_660) | ~m1_subset_1(D_660, k1_zfmisc_1(k2_zfmisc_1(A_658, B_659))) | r2_hidden(k4_tarski('#skF_2'(A_658, B_659, D_660, D_660), '#skF_3'(A_658, B_659, D_660, D_660)), D_660))), inference(factorization, [status(thm), theory('equality')], [c_40])).
% 12.09/4.64  tff(c_34, plain, (![A_22, B_23, C_24, D_38]: (~r2_hidden(k4_tarski('#skF_2'(A_22, B_23, C_24, D_38), '#skF_3'(A_22, B_23, C_24, D_38)), D_38) | ~r2_hidden(k4_tarski('#skF_2'(A_22, B_23, C_24, D_38), '#skF_3'(A_22, B_23, C_24, D_38)), C_24) | r2_relset_1(A_22, B_23, C_24, D_38) | ~m1_subset_1(D_38, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 12.09/4.64  tff(c_11245, plain, (![A_841, B_842, D_843]: (~r2_hidden(k4_tarski('#skF_2'(A_841, B_842, D_843, D_843), '#skF_3'(A_841, B_842, D_843, D_843)), D_843) | r2_relset_1(A_841, B_842, D_843, D_843) | ~m1_subset_1(D_843, k1_zfmisc_1(k2_zfmisc_1(A_841, B_842))))), inference(resolution, [status(thm)], [c_8562, c_34])).
% 12.09/4.64  tff(c_11264, plain, (![A_844, B_845, D_846]: (r2_relset_1(A_844, B_845, D_846, D_846) | ~m1_subset_1(D_846, k1_zfmisc_1(k2_zfmisc_1(A_844, B_845))))), inference(resolution, [status(thm)], [c_6389, c_11245])).
% 12.09/4.64  tff(c_11335, plain, (r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_70, c_11264])).
% 12.09/4.64  tff(c_11367, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1590, c_11335])).
% 12.09/4.64  tff(c_11368, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_490])).
% 12.09/4.64  tff(c_14, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.09/4.64  tff(c_108, plain, (![A_69, B_70]: (r1_tarski(A_69, B_70) | ~m1_subset_1(A_69, k1_zfmisc_1(B_70)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.09/4.64  tff(c_124, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(resolution, [status(thm)], [c_14, c_108])).
% 12.09/4.64  tff(c_11387, plain, (![A_5]: (r1_tarski('#skF_5', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_11368, c_124])).
% 12.09/4.64  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.09/4.64  tff(c_11390, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_11368, c_11368, c_10])).
% 12.09/4.64  tff(c_123, plain, (r1_tarski('#skF_7', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_64, c_108])).
% 12.09/4.64  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.09/4.64  tff(c_138, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_7' | ~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_7')), inference(resolution, [status(thm)], [c_123, c_2])).
% 12.09/4.64  tff(c_249, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_7')), inference(splitLeft, [status(thm)], [c_138])).
% 12.09/4.64  tff(c_11461, plain, (~r1_tarski('#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_11390, c_249])).
% 12.09/4.64  tff(c_11469, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11387, c_11461])).
% 12.09/4.64  tff(c_11470, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_487])).
% 12.09/4.64  tff(c_11497, plain, (![A_5]: (r1_tarski('#skF_5', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_11470, c_124])).
% 12.09/4.64  tff(c_11500, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_11470, c_11470, c_10])).
% 12.09/4.64  tff(c_11544, plain, (~r1_tarski('#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_11500, c_249])).
% 12.09/4.64  tff(c_11552, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11497, c_11544])).
% 12.09/4.64  tff(c_11553, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_7'), inference(splitRight, [status(thm)], [c_138])).
% 12.09/4.64  tff(c_11559, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_11553, c_64])).
% 12.09/4.64  tff(c_11644, plain, (![A_862, B_863, C_864]: (k1_relset_1(A_862, B_863, C_864)=k1_relat_1(C_864) | ~m1_subset_1(C_864, k1_zfmisc_1(k2_zfmisc_1(A_862, B_863))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 12.09/4.64  tff(c_11672, plain, (![C_867]: (k1_relset_1('#skF_4', '#skF_5', C_867)=k1_relat_1(C_867) | ~m1_subset_1(C_867, k1_zfmisc_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_11553, c_11644])).
% 12.09/4.64  tff(c_11688, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_11559, c_11672])).
% 12.09/4.64  tff(c_11768, plain, (![B_882, C_883, A_884]: (k1_xboole_0=B_882 | v1_funct_2(C_883, A_884, B_882) | k1_relset_1(A_884, B_882, C_883)!=A_884 | ~m1_subset_1(C_883, k1_zfmisc_1(k2_zfmisc_1(A_884, B_882))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 12.09/4.64  tff(c_11771, plain, (![C_883]: (k1_xboole_0='#skF_5' | v1_funct_2(C_883, '#skF_4', '#skF_5') | k1_relset_1('#skF_4', '#skF_5', C_883)!='#skF_4' | ~m1_subset_1(C_883, k1_zfmisc_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_11553, c_11768])).
% 12.09/4.64  tff(c_11898, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_11771])).
% 12.09/4.64  tff(c_8, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.09/4.64  tff(c_11568, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0!='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_11553, c_8])).
% 12.09/4.64  tff(c_11671, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_11568])).
% 12.09/4.64  tff(c_11911, plain, ('#skF_7'!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_11898, c_11671])).
% 12.09/4.64  tff(c_11922, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_11898, c_11898, c_10])).
% 12.09/4.64  tff(c_12017, plain, ('#skF_7'='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_11922, c_11553])).
% 12.09/4.64  tff(c_12019, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11911, c_12017])).
% 12.09/4.64  tff(c_12021, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_11771])).
% 12.09/4.64  tff(c_11865, plain, (![B_896, A_897, C_898]: (k1_xboole_0=B_896 | k1_relset_1(A_897, B_896, C_898)=A_897 | ~v1_funct_2(C_898, A_897, B_896) | ~m1_subset_1(C_898, k1_zfmisc_1(k2_zfmisc_1(A_897, B_896))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 12.09/4.64  tff(c_11868, plain, (![C_898]: (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', C_898)='#skF_4' | ~v1_funct_2(C_898, '#skF_4', '#skF_5') | ~m1_subset_1(C_898, k1_zfmisc_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_11553, c_11865])).
% 12.09/4.64  tff(c_12022, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_11868])).
% 12.09/4.64  tff(c_12023, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12021, c_12022])).
% 12.09/4.64  tff(c_12050, plain, (![C_910]: (k1_relset_1('#skF_4', '#skF_5', C_910)='#skF_4' | ~v1_funct_2(C_910, '#skF_4', '#skF_5') | ~m1_subset_1(C_910, k1_zfmisc_1('#skF_7')))), inference(splitRight, [status(thm)], [c_11868])).
% 12.09/4.64  tff(c_12056, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_11559, c_12050])).
% 12.09/4.64  tff(c_12070, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_11688, c_12056])).
% 12.09/4.64  tff(c_11558, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_11553, c_70])).
% 12.09/4.64  tff(c_11687, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_11558, c_11672])).
% 12.09/4.64  tff(c_12053, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_11558, c_12050])).
% 12.09/4.64  tff(c_12067, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_11687, c_12053])).
% 12.09/4.64  tff(c_26, plain, (![A_13, B_17]: (r2_hidden('#skF_1'(A_13, B_17), k1_relat_1(A_13)) | B_17=A_13 | k1_relat_1(B_17)!=k1_relat_1(A_13) | ~v1_funct_1(B_17) | ~v1_relat_1(B_17) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.09/4.64  tff(c_12078, plain, (![B_17]: (r2_hidden('#skF_1'('#skF_6', B_17), '#skF_4') | B_17='#skF_6' | k1_relat_1(B_17)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_17) | ~v1_relat_1(B_17) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_12067, c_26])).
% 12.09/4.64  tff(c_12180, plain, (![B_916]: (r2_hidden('#skF_1'('#skF_6', B_916), '#skF_4') | B_916='#skF_6' | k1_relat_1(B_916)!='#skF_4' | ~v1_funct_1(B_916) | ~v1_relat_1(B_916))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_74, c_12067, c_12078])).
% 12.09/4.64  tff(c_12196, plain, (![B_918]: (m1_subset_1('#skF_1'('#skF_6', B_918), '#skF_4') | B_918='#skF_6' | k1_relat_1(B_918)!='#skF_4' | ~v1_funct_1(B_918) | ~v1_relat_1(B_918))), inference(resolution, [status(thm)], [c_12180, c_16])).
% 12.09/4.64  tff(c_12364, plain, (![B_935]: (k1_funct_1('#skF_7', '#skF_1'('#skF_6', B_935))=k1_funct_1('#skF_6', '#skF_1'('#skF_6', B_935)) | B_935='#skF_6' | k1_relat_1(B_935)!='#skF_4' | ~v1_funct_1(B_935) | ~v1_relat_1(B_935))), inference(resolution, [status(thm)], [c_12196, c_62])).
% 12.09/4.64  tff(c_12371, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_7'='#skF_6' | k1_relat_1('#skF_7')!='#skF_4' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_12364, c_24])).
% 12.09/4.64  tff(c_12378, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_177, c_68, c_12070, c_176, c_74, c_12070, c_12067, c_12371])).
% 12.09/4.64  tff(c_122, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_70, c_108])).
% 12.09/4.64  tff(c_141, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_6' | ~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_122, c_2])).
% 12.09/4.64  tff(c_215, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_141])).
% 12.09/4.64  tff(c_11555, plain, (~r1_tarski('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11553, c_215])).
% 12.09/4.64  tff(c_12397, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_12378, c_11555])).
% 12.09/4.64  tff(c_12409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_12397])).
% 12.09/4.64  tff(c_12411, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_11568])).
% 12.09/4.64  tff(c_12419, plain, (![A_5]: (r1_tarski('#skF_7', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_12411, c_124])).
% 12.09/4.64  tff(c_12431, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12419, c_11555])).
% 12.09/4.64  tff(c_12432, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_141])).
% 12.09/4.64  tff(c_12437, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_12432, c_64])).
% 12.09/4.64  tff(c_12479, plain, (![A_942, B_943, C_944]: (k1_relset_1(A_942, B_943, C_944)=k1_relat_1(C_944) | ~m1_subset_1(C_944, k1_zfmisc_1(k2_zfmisc_1(A_942, B_943))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 12.09/4.64  tff(c_12625, plain, (![C_967]: (k1_relset_1('#skF_4', '#skF_5', C_967)=k1_relat_1(C_967) | ~m1_subset_1(C_967, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_12432, c_12479])).
% 12.09/4.64  tff(c_12640, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_12437, c_12625])).
% 12.09/4.64  tff(c_12740, plain, (![B_980, C_981, A_982]: (k1_xboole_0=B_980 | v1_funct_2(C_981, A_982, B_980) | k1_relset_1(A_982, B_980, C_981)!=A_982 | ~m1_subset_1(C_981, k1_zfmisc_1(k2_zfmisc_1(A_982, B_980))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 12.09/4.64  tff(c_12743, plain, (![C_981]: (k1_xboole_0='#skF_5' | v1_funct_2(C_981, '#skF_4', '#skF_5') | k1_relset_1('#skF_4', '#skF_5', C_981)!='#skF_4' | ~m1_subset_1(C_981, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_12432, c_12740])).
% 12.09/4.64  tff(c_12778, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_12743])).
% 12.09/4.64  tff(c_12442, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0!='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_12432, c_8])).
% 12.09/4.64  tff(c_12478, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_12442])).
% 12.09/4.64  tff(c_12791, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_12778, c_12478])).
% 12.09/4.64  tff(c_12884, plain, (![A_990]: (k2_zfmisc_1(A_990, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12778, c_12778, c_10])).
% 12.09/4.64  tff(c_12904, plain, ('#skF_5'='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_12884, c_12432])).
% 12.09/4.64  tff(c_12916, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12791, c_12904])).
% 12.09/4.64  tff(c_12918, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_12743])).
% 12.09/4.64  tff(c_12942, plain, (![B_992, A_993, C_994]: (k1_xboole_0=B_992 | k1_relset_1(A_993, B_992, C_994)=A_993 | ~v1_funct_2(C_994, A_993, B_992) | ~m1_subset_1(C_994, k1_zfmisc_1(k2_zfmisc_1(A_993, B_992))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 12.09/4.64  tff(c_12945, plain, (![C_994]: (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', C_994)='#skF_4' | ~v1_funct_2(C_994, '#skF_4', '#skF_5') | ~m1_subset_1(C_994, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_12432, c_12942])).
% 12.09/4.64  tff(c_12992, plain, (![C_998]: (k1_relset_1('#skF_4', '#skF_5', C_998)='#skF_4' | ~v1_funct_2(C_998, '#skF_4', '#skF_5') | ~m1_subset_1(C_998, k1_zfmisc_1('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_12918, c_12945])).
% 12.09/4.64  tff(c_12995, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_12437, c_12992])).
% 12.09/4.64  tff(c_13009, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_12640, c_12995])).
% 12.09/4.64  tff(c_12436, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_12432, c_70])).
% 12.09/4.64  tff(c_12641, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_12436, c_12625])).
% 12.09/4.64  tff(c_12998, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_12436, c_12992])).
% 12.09/4.64  tff(c_13012, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_12641, c_12998])).
% 12.09/4.64  tff(c_13071, plain, (![A_1000, B_1001]: (r2_hidden('#skF_1'(A_1000, B_1001), k1_relat_1(A_1000)) | B_1001=A_1000 | k1_relat_1(B_1001)!=k1_relat_1(A_1000) | ~v1_funct_1(B_1001) | ~v1_relat_1(B_1001) | ~v1_funct_1(A_1000) | ~v1_relat_1(A_1000))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.09/4.64  tff(c_13079, plain, (![B_1001]: (r2_hidden('#skF_1'('#skF_6', B_1001), '#skF_4') | B_1001='#skF_6' | k1_relat_1(B_1001)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_1001) | ~v1_relat_1(B_1001) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_13012, c_13071])).
% 12.09/4.64  tff(c_13089, plain, (![B_1002]: (r2_hidden('#skF_1'('#skF_6', B_1002), '#skF_4') | B_1002='#skF_6' | k1_relat_1(B_1002)!='#skF_4' | ~v1_funct_1(B_1002) | ~v1_relat_1(B_1002))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_74, c_13012, c_13079])).
% 12.09/4.64  tff(c_13105, plain, (![B_1004]: (m1_subset_1('#skF_1'('#skF_6', B_1004), '#skF_4') | B_1004='#skF_6' | k1_relat_1(B_1004)!='#skF_4' | ~v1_funct_1(B_1004) | ~v1_relat_1(B_1004))), inference(resolution, [status(thm)], [c_13089, c_16])).
% 12.09/4.64  tff(c_13109, plain, (![B_1004]: (k1_funct_1('#skF_7', '#skF_1'('#skF_6', B_1004))=k1_funct_1('#skF_6', '#skF_1'('#skF_6', B_1004)) | B_1004='#skF_6' | k1_relat_1(B_1004)!='#skF_4' | ~v1_funct_1(B_1004) | ~v1_relat_1(B_1004))), inference(resolution, [status(thm)], [c_13105, c_62])).
% 12.09/4.64  tff(c_13484, plain, (![B_1029, A_1030]: (k1_funct_1(B_1029, '#skF_1'(A_1030, B_1029))!=k1_funct_1(A_1030, '#skF_1'(A_1030, B_1029)) | B_1029=A_1030 | k1_relat_1(B_1029)!=k1_relat_1(A_1030) | ~v1_funct_1(B_1029) | ~v1_relat_1(B_1029) | ~v1_funct_1(A_1030) | ~v1_relat_1(A_1030))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.09/4.64  tff(c_13491, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_7'='#skF_6' | k1_relat_1('#skF_7')!='#skF_4' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_13109, c_13484])).
% 12.09/4.64  tff(c_13496, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_177, c_68, c_13009, c_176, c_74, c_13012, c_13009, c_13491])).
% 12.09/4.64  tff(c_12435, plain, (r1_tarski('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_12432, c_123])).
% 12.09/4.64  tff(c_12450, plain, ('#skF_7'='#skF_6' | ~r1_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_12435, c_2])).
% 12.09/4.64  tff(c_12476, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_12450])).
% 12.09/4.64  tff(c_13504, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_13496, c_12476])).
% 12.09/4.64  tff(c_13517, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_13504])).
% 12.09/4.64  tff(c_13519, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_12442])).
% 12.09/4.64  tff(c_13526, plain, (![A_5]: (r1_tarski('#skF_6', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_13519, c_124])).
% 12.09/4.64  tff(c_13538, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13526, c_12476])).
% 12.09/4.64  tff(c_13539, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_12450])).
% 12.09/4.64  tff(c_13541, plain, ('#skF_7'='#skF_6' | ~r1_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_12432, c_12432, c_138])).
% 12.09/4.64  tff(c_13542, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_13541])).
% 12.09/4.64  tff(c_13561, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_13539, c_13542])).
% 12.09/4.64  tff(c_13562, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_13541])).
% 12.09/4.64  tff(c_13569, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_13562, c_60])).
% 12.09/4.64  tff(c_15085, plain, (![A_22, B_23, C_24]: (r2_relset_1(A_22, B_23, C_24, C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | r2_hidden(k4_tarski('#skF_2'(A_22, B_23, C_24, C_24), '#skF_3'(A_22, B_23, C_24, C_24)), C_24))), inference(factorization, [status(thm), theory('equality')], [c_40])).
% 12.09/4.64  tff(c_16607, plain, (![A_1286, B_1287, C_1288]: (r2_relset_1(A_1286, B_1287, C_1288, C_1288) | ~m1_subset_1(C_1288, k1_zfmisc_1(k2_zfmisc_1(A_1286, B_1287))) | r2_hidden(k4_tarski('#skF_2'(A_1286, B_1287, C_1288, C_1288), '#skF_3'(A_1286, B_1287, C_1288, C_1288)), C_1288))), inference(factorization, [status(thm), theory('equality')], [c_40])).
% 12.09/4.64  tff(c_19849, plain, (![A_1520, B_1521, C_1522]: (~r2_hidden(k4_tarski('#skF_2'(A_1520, B_1521, C_1522, C_1522), '#skF_3'(A_1520, B_1521, C_1522, C_1522)), C_1522) | r2_relset_1(A_1520, B_1521, C_1522, C_1522) | ~m1_subset_1(C_1522, k1_zfmisc_1(k2_zfmisc_1(A_1520, B_1521))))), inference(resolution, [status(thm)], [c_16607, c_34])).
% 12.09/4.64  tff(c_19868, plain, (![A_1523, B_1524, C_1525]: (r2_relset_1(A_1523, B_1524, C_1525, C_1525) | ~m1_subset_1(C_1525, k1_zfmisc_1(k2_zfmisc_1(A_1523, B_1524))))), inference(resolution, [status(thm)], [c_15085, c_19849])).
% 12.09/4.64  tff(c_19968, plain, (![C_1526]: (r2_relset_1('#skF_4', '#skF_5', C_1526, C_1526) | ~m1_subset_1(C_1526, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_12432, c_19868])).
% 12.09/4.64  tff(c_20036, plain, (r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_12436, c_19968])).
% 12.09/4.64  tff(c_20066, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13569, c_20036])).
% 12.09/4.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.09/4.64  
% 12.09/4.64  Inference rules
% 12.09/4.64  ----------------------
% 12.09/4.64  #Ref     : 8
% 12.09/4.64  #Sup     : 4182
% 12.09/4.64  #Fact    : 10
% 12.09/4.64  #Define  : 0
% 12.09/4.64  #Split   : 68
% 12.09/4.64  #Chain   : 0
% 12.09/4.64  #Close   : 0
% 12.09/4.64  
% 12.09/4.64  Ordering : KBO
% 12.09/4.64  
% 12.09/4.64  Simplification rules
% 12.09/4.64  ----------------------
% 12.09/4.64  #Subsume      : 484
% 12.09/4.64  #Demod        : 2171
% 12.09/4.64  #Tautology    : 717
% 12.09/4.64  #SimpNegUnit  : 112
% 12.09/4.64  #BackRed      : 355
% 12.09/4.64  
% 12.09/4.64  #Partial instantiations: 0
% 12.09/4.64  #Strategies tried      : 1
% 12.09/4.64  
% 12.09/4.64  Timing (in seconds)
% 12.09/4.64  ----------------------
% 12.09/4.64  Preprocessing        : 0.35
% 12.09/4.64  Parsing              : 0.18
% 12.09/4.64  CNF conversion       : 0.03
% 12.09/4.65  Main loop            : 3.49
% 12.09/4.65  Inferencing          : 1.00
% 12.09/4.65  Reduction            : 1.11
% 12.09/4.65  Demodulation         : 0.80
% 12.09/4.65  BG Simplification    : 0.13
% 12.09/4.65  Subsumption          : 0.96
% 12.09/4.65  Abstraction          : 0.16
% 12.09/4.65  MUC search           : 0.00
% 12.09/4.65  Cooper               : 0.00
% 12.09/4.65  Total                : 3.90
% 12.09/4.65  Index Insertion      : 0.00
% 12.09/4.65  Index Deletion       : 0.00
% 12.09/4.65  Index Matching       : 0.00
% 12.09/4.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
