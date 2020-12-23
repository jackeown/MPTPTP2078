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
% DateTime   : Thu Dec  3 10:12:09 EST 2020

% Result     : Theorem 9.24s
% Output     : CNFRefutation 9.31s
% Verified   : 
% Statistics : Number of formulae       :  228 (1658 expanded)
%              Number of leaves         :   54 ( 569 expanded)
%              Depth                    :   19
%              Number of atoms          :  435 (4310 expanded)
%              Number of equality atoms :  111 (1183 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

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

tff(f_199,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
             => ( v2_funct_1(C)
                & v2_funct_2(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_140,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_75,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_138,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_92,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_134,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_114,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_179,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_157,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( r2_relset_1(B,B,k1_partfun1(B,A,A,B,D,C),k6_partfun1(B))
           => k2_relset_1(A,B,C) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_122,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_76,plain,
    ( ~ v2_funct_2('#skF_7','#skF_4')
    | ~ v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_126,plain,(
    ~ v2_funct_1('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( v1_xboole_0(k2_zfmisc_1(A_9,B_10))
      | ~ v1_xboole_0(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_80,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_256,plain,(
    ! [C_88,B_89,A_90] :
      ( ~ v1_xboole_0(C_88)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(C_88))
      | ~ r2_hidden(A_90,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_264,plain,(
    ! [A_90] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_4'))
      | ~ r2_hidden(A_90,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_80,c_256])).

tff(c_319,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_264])).

tff(c_323,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_319])).

tff(c_68,plain,(
    ! [A_48] : k6_relat_1(A_48) = k6_partfun1(A_48) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_28,plain,(
    ! [A_17] : k1_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_93,plain,(
    ! [A_17] : k1_relat_1(k6_partfun1(A_17)) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_28])).

tff(c_66,plain,(
    ! [A_47] : m1_subset_1(k6_partfun1(A_47),k1_zfmisc_1(k2_zfmisc_1(A_47,A_47))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_183,plain,(
    ! [C_83,A_84,B_85] :
      ( v1_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_214,plain,(
    ! [A_86] : v1_relat_1(k6_partfun1(A_86)) ),
    inference(resolution,[status(thm)],[c_66,c_183])).

tff(c_26,plain,(
    ! [A_16] :
      ( k1_relat_1(A_16) != k1_xboole_0
      | k1_xboole_0 = A_16
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_217,plain,(
    ! [A_86] :
      ( k1_relat_1(k6_partfun1(A_86)) != k1_xboole_0
      | k6_partfun1(A_86) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_214,c_26])).

tff(c_228,plain,(
    ! [A_87] :
      ( k1_xboole_0 != A_87
      | k6_partfun1(A_87) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_217])).

tff(c_78,plain,(
    r2_relset_1('#skF_4','#skF_4',k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7'),k6_partfun1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_236,plain,
    ( r2_relset_1('#skF_4','#skF_4',k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7'),k1_xboole_0)
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_78])).

tff(c_347,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_236])).

tff(c_90,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_88,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_86,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_84,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_82,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_42,plain,(
    ! [A_25] : v2_funct_1(k6_relat_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_91,plain,(
    ! [A_25] : v2_funct_1(k6_partfun1(A_25)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_42])).

tff(c_60,plain,(
    ! [D_44,F_46,C_43,A_41,B_42,E_45] :
      ( m1_subset_1(k1_partfun1(A_41,B_42,C_43,D_44,E_45,F_46),k1_zfmisc_1(k2_zfmisc_1(A_41,D_44)))
      | ~ m1_subset_1(F_46,k1_zfmisc_1(k2_zfmisc_1(C_43,D_44)))
      | ~ v1_funct_1(F_46)
      | ~ m1_subset_1(E_45,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42)))
      | ~ v1_funct_1(E_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1003,plain,(
    ! [D_160,C_161,A_162,B_163] :
      ( D_160 = C_161
      | ~ r2_relset_1(A_162,B_163,C_161,D_160)
      | ~ m1_subset_1(D_160,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163)))
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1011,plain,
    ( k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7') = k6_partfun1('#skF_4')
    | ~ m1_subset_1(k6_partfun1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
    | ~ m1_subset_1(k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_78,c_1003])).

tff(c_1026,plain,
    ( k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7') = k6_partfun1('#skF_4')
    | ~ m1_subset_1(k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1011])).

tff(c_1291,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_1026])).

tff(c_1953,plain,
    ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_1291])).

tff(c_1957,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_84,c_80,c_1953])).

tff(c_1958,plain,(
    k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7') = k6_partfun1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1026])).

tff(c_2871,plain,(
    ! [A_296,E_299,B_297,C_295,D_298] :
      ( k1_xboole_0 = C_295
      | v2_funct_1(D_298)
      | ~ v2_funct_1(k1_partfun1(A_296,B_297,B_297,C_295,D_298,E_299))
      | ~ m1_subset_1(E_299,k1_zfmisc_1(k2_zfmisc_1(B_297,C_295)))
      | ~ v1_funct_2(E_299,B_297,C_295)
      | ~ v1_funct_1(E_299)
      | ~ m1_subset_1(D_298,k1_zfmisc_1(k2_zfmisc_1(A_296,B_297)))
      | ~ v1_funct_2(D_298,A_296,B_297)
      | ~ v1_funct_1(D_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_2873,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_funct_1('#skF_6')
    | ~ v2_funct_1(k6_partfun1('#skF_4'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1958,c_2871])).

tff(c_2878,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_84,c_82,c_80,c_91,c_2873])).

tff(c_2880,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_347,c_2878])).

tff(c_2882,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_236])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2896,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2882,c_6])).

tff(c_2898,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_323,c_2896])).

tff(c_2901,plain,(
    ! [A_300] : ~ r2_hidden(A_300,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_264])).

tff(c_2906,plain,(
    v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_4,c_2901])).

tff(c_127,plain,(
    ! [B_69,A_70] :
      ( ~ v1_xboole_0(B_69)
      | B_69 = A_70
      | ~ v1_xboole_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_130,plain,(
    ! [A_70] :
      ( k1_xboole_0 = A_70
      | ~ v1_xboole_0(A_70) ) ),
    inference(resolution,[status(thm)],[c_6,c_127])).

tff(c_2915,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_2906,c_130])).

tff(c_30,plain,(
    ! [A_17] : k2_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_92,plain,(
    ! [A_17] : k2_relat_1(k6_partfun1(A_17)) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_30])).

tff(c_248,plain,(
    ! [A_87] :
      ( k2_relat_1(k1_xboole_0) = A_87
      | k1_xboole_0 != A_87 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_92])).

tff(c_3073,plain,(
    k2_relat_1('#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2915,c_2915,c_248])).

tff(c_196,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_80,c_183])).

tff(c_24,plain,(
    ! [A_16] :
      ( k2_relat_1(A_16) != k1_xboole_0
      | k1_xboole_0 = A_16
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_205,plain,
    ( k2_relat_1('#skF_7') != k1_xboole_0
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_196,c_24])).

tff(c_225,plain,(
    k2_relat_1('#skF_7') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_205])).

tff(c_2921,plain,(
    k2_relat_1('#skF_7') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2915,c_225])).

tff(c_3076,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3073,c_2921])).

tff(c_3077,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_205])).

tff(c_220,plain,(
    ! [A_86] :
      ( k2_relat_1(k6_partfun1(A_86)) != k1_xboole_0
      | k6_partfun1(A_86) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_214,c_24])).

tff(c_224,plain,(
    ! [A_86] :
      ( k1_xboole_0 != A_86
      | k6_partfun1(A_86) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_220])).

tff(c_5546,plain,(
    ! [A_515] :
      ( A_515 != '#skF_7'
      | k6_partfun1(A_515) = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3077,c_3077,c_224])).

tff(c_5557,plain,
    ( r2_relset_1('#skF_4','#skF_4',k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7'),'#skF_7')
    | '#skF_7' != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_5546,c_78])).

tff(c_5579,plain,(
    '#skF_7' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5557])).

tff(c_3093,plain,(
    ! [C_310,B_311,A_312] :
      ( ~ v1_xboole_0(C_310)
      | ~ m1_subset_1(B_311,k1_zfmisc_1(C_310))
      | ~ r2_hidden(A_312,B_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3101,plain,(
    ! [A_312] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_4'))
      | ~ r2_hidden(A_312,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_80,c_3093])).

tff(c_3118,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3101])).

tff(c_3122,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_3118])).

tff(c_3155,plain,(
    ! [A_317] :
      ( A_317 != '#skF_7'
      | k6_partfun1(A_317) = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3077,c_3077,c_224])).

tff(c_3163,plain,
    ( r2_relset_1('#skF_4','#skF_4',k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7'),'#skF_7')
    | '#skF_7' != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3155,c_78])).

tff(c_3265,plain,(
    '#skF_7' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3163])).

tff(c_3690,plain,(
    ! [D_377,C_378,A_379,B_380] :
      ( D_377 = C_378
      | ~ r2_relset_1(A_379,B_380,C_378,D_377)
      | ~ m1_subset_1(D_377,k1_zfmisc_1(k2_zfmisc_1(A_379,B_380)))
      | ~ m1_subset_1(C_378,k1_zfmisc_1(k2_zfmisc_1(A_379,B_380))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_3696,plain,
    ( k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7') = k6_partfun1('#skF_4')
    | ~ m1_subset_1(k6_partfun1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
    | ~ m1_subset_1(k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_78,c_3690])).

tff(c_3707,plain,
    ( k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7') = k6_partfun1('#skF_4')
    | ~ m1_subset_1(k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3696])).

tff(c_3977,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_3707])).

tff(c_4678,plain,
    ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_3977])).

tff(c_4682,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_84,c_80,c_4678])).

tff(c_4683,plain,(
    k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7') = k6_partfun1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_3707])).

tff(c_74,plain,(
    ! [C_56,E_59,D_57,B_55,A_54] :
      ( k1_xboole_0 = C_56
      | v2_funct_1(D_57)
      | ~ v2_funct_1(k1_partfun1(A_54,B_55,B_55,C_56,D_57,E_59))
      | ~ m1_subset_1(E_59,k1_zfmisc_1(k2_zfmisc_1(B_55,C_56)))
      | ~ v1_funct_2(E_59,B_55,C_56)
      | ~ v1_funct_1(E_59)
      | ~ m1_subset_1(D_57,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55)))
      | ~ v1_funct_2(D_57,A_54,B_55)
      | ~ v1_funct_1(D_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_5438,plain,(
    ! [D_507,E_508,A_505,C_504,B_506] :
      ( C_504 = '#skF_7'
      | v2_funct_1(D_507)
      | ~ v2_funct_1(k1_partfun1(A_505,B_506,B_506,C_504,D_507,E_508))
      | ~ m1_subset_1(E_508,k1_zfmisc_1(k2_zfmisc_1(B_506,C_504)))
      | ~ v1_funct_2(E_508,B_506,C_504)
      | ~ v1_funct_1(E_508)
      | ~ m1_subset_1(D_507,k1_zfmisc_1(k2_zfmisc_1(A_505,B_506)))
      | ~ v1_funct_2(D_507,A_505,B_506)
      | ~ v1_funct_1(D_507) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3077,c_74])).

tff(c_5440,plain,
    ( '#skF_7' = '#skF_4'
    | v2_funct_1('#skF_6')
    | ~ v2_funct_1(k6_partfun1('#skF_4'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_4683,c_5438])).

tff(c_5445,plain,
    ( '#skF_7' = '#skF_4'
    | v2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_84,c_82,c_80,c_91,c_5440])).

tff(c_5447,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_3265,c_5445])).

tff(c_5449,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3163])).

tff(c_3085,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3077,c_6])).

tff(c_5462,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5449,c_3085])).

tff(c_5470,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3122,c_5462])).

tff(c_5472,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3101])).

tff(c_3084,plain,(
    ! [A_70] :
      ( A_70 = '#skF_7'
      | ~ v1_xboole_0(A_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3077,c_130])).

tff(c_5485,plain,(
    k2_zfmisc_1('#skF_5','#skF_4') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_5472,c_3084])).

tff(c_5493,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5485,c_80])).

tff(c_7186,plain,(
    ! [C_647,F_649,E_645,D_648,B_650,A_646] :
      ( m1_subset_1(k1_partfun1(A_646,B_650,C_647,D_648,E_645,F_649),k1_zfmisc_1(k2_zfmisc_1(A_646,D_648)))
      | ~ m1_subset_1(F_649,k1_zfmisc_1(k2_zfmisc_1(C_647,D_648)))
      | ~ v1_funct_1(F_649)
      | ~ m1_subset_1(E_645,k1_zfmisc_1(k2_zfmisc_1(A_646,B_650)))
      | ~ v1_funct_1(E_645) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_6416,plain,(
    ! [D_596,C_597,A_598,B_599] :
      ( D_596 = C_597
      | ~ r2_relset_1(A_598,B_599,C_597,D_596)
      | ~ m1_subset_1(D_596,k1_zfmisc_1(k2_zfmisc_1(A_598,B_599)))
      | ~ m1_subset_1(C_597,k1_zfmisc_1(k2_zfmisc_1(A_598,B_599))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_6424,plain,
    ( k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7') = k6_partfun1('#skF_4')
    | ~ m1_subset_1(k6_partfun1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
    | ~ m1_subset_1(k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_78,c_6416])).

tff(c_6439,plain,
    ( k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7') = k6_partfun1('#skF_4')
    | ~ m1_subset_1(k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_6424])).

tff(c_6625,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_6439])).

tff(c_7194,plain,
    ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_7186,c_6625])).

tff(c_7228,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_84,c_5493,c_5485,c_7194])).

tff(c_7229,plain,(
    k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7') = k6_partfun1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_6439])).

tff(c_8664,plain,(
    ! [C_738,A_739,D_741,B_740,E_742] :
      ( C_738 = '#skF_7'
      | v2_funct_1(D_741)
      | ~ v2_funct_1(k1_partfun1(A_739,B_740,B_740,C_738,D_741,E_742))
      | ~ m1_subset_1(E_742,k1_zfmisc_1(k2_zfmisc_1(B_740,C_738)))
      | ~ v1_funct_2(E_742,B_740,C_738)
      | ~ v1_funct_1(E_742)
      | ~ m1_subset_1(D_741,k1_zfmisc_1(k2_zfmisc_1(A_739,B_740)))
      | ~ v1_funct_2(D_741,A_739,B_740)
      | ~ v1_funct_1(D_741) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3077,c_74])).

tff(c_8666,plain,
    ( '#skF_7' = '#skF_4'
    | v2_funct_1('#skF_6')
    | ~ v2_funct_1(k6_partfun1('#skF_4'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_7229,c_8664])).

tff(c_8671,plain,
    ( '#skF_7' = '#skF_4'
    | v2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_84,c_82,c_5493,c_5485,c_91,c_8666])).

tff(c_8673,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_5579,c_8671])).

tff(c_8675,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5557])).

tff(c_5571,plain,(
    ! [A_515] :
      ( v2_funct_1('#skF_7')
      | A_515 != '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5546,c_91])).

tff(c_8758,plain,(
    ! [A_515] :
      ( v2_funct_1('#skF_4')
      | A_515 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8675,c_8675,c_5571])).

tff(c_8759,plain,(
    ! [A_515] : A_515 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_8758])).

tff(c_135,plain,(
    ! [A_73] :
      ( k1_xboole_0 = A_73
      | ~ v1_xboole_0(A_73) ) ),
    inference(resolution,[status(thm)],[c_6,c_127])).

tff(c_150,plain,(
    ! [A_75,B_76] :
      ( k2_zfmisc_1(A_75,B_76) = k1_xboole_0
      | ~ v1_xboole_0(B_76) ) ),
    inference(resolution,[status(thm)],[c_16,c_135])).

tff(c_156,plain,(
    ! [A_75] : k2_zfmisc_1(A_75,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_150])).

tff(c_3082,plain,(
    ! [A_75] : k2_zfmisc_1(A_75,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3077,c_3077,c_156])).

tff(c_8678,plain,(
    ! [A_75] : k2_zfmisc_1(A_75,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8675,c_8675,c_3082])).

tff(c_8765,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8759,c_8678])).

tff(c_8766,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_8758])).

tff(c_8684,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8675,c_3077])).

tff(c_197,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_86,c_183])).

tff(c_212,plain,
    ( k1_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_197,c_26])).

tff(c_8801,plain,
    ( k1_relat_1('#skF_6') != '#skF_4'
    | '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8684,c_8684,c_212])).

tff(c_8802,plain,(
    k1_relat_1('#skF_6') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_8801])).

tff(c_5528,plain,(
    ! [C_511,A_512,B_513] :
      ( v4_relat_1(C_511,A_512)
      | ~ m1_subset_1(C_511,k1_zfmisc_1(k2_zfmisc_1(A_512,B_513))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_5542,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_5528])).

tff(c_22,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k1_relat_1(B_15),A_14)
      | ~ v4_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_8683,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8675,c_3085])).

tff(c_8677,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8675,c_8675,c_5493])).

tff(c_5531,plain,(
    ! [C_511,A_75] :
      ( v4_relat_1(C_511,A_75)
      | ~ m1_subset_1(C_511,k1_zfmisc_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3082,c_5528])).

tff(c_8986,plain,(
    ! [C_774,A_775] :
      ( v4_relat_1(C_774,A_775)
      | ~ m1_subset_1(C_774,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8675,c_5531])).

tff(c_8989,plain,(
    ! [A_775] : v4_relat_1('#skF_4',A_775) ),
    inference(resolution,[status(thm)],[c_8677,c_8986])).

tff(c_9006,plain,(
    ! [A_781,A_782] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_781,A_781))
      | ~ r2_hidden(A_782,k6_partfun1(A_781)) ) ),
    inference(resolution,[status(thm)],[c_66,c_3093])).

tff(c_9016,plain,(
    ! [A_783,B_784] :
      ( ~ r2_hidden(A_783,k6_partfun1(B_784))
      | ~ v1_xboole_0(B_784) ) ),
    inference(resolution,[status(thm)],[c_16,c_9006])).

tff(c_9034,plain,(
    ! [B_788] :
      ( ~ v1_xboole_0(B_788)
      | v1_xboole_0(k6_partfun1(B_788)) ) ),
    inference(resolution,[status(thm)],[c_4,c_9016])).

tff(c_8681,plain,(
    ! [A_70] :
      ( A_70 = '#skF_4'
      | ~ v1_xboole_0(A_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8675,c_3084])).

tff(c_9052,plain,(
    ! [B_789] :
      ( k6_partfun1(B_789) = '#skF_4'
      | ~ v1_xboole_0(B_789) ) ),
    inference(resolution,[status(thm)],[c_9034,c_8681])).

tff(c_9331,plain,(
    ! [A_810,B_811] :
      ( k6_partfun1(k2_zfmisc_1(A_810,B_811)) = '#skF_4'
      | ~ v1_xboole_0(B_811) ) ),
    inference(resolution,[status(thm)],[c_16,c_9052])).

tff(c_195,plain,(
    ! [A_47] : v1_relat_1(k6_partfun1(A_47)) ),
    inference(resolution,[status(thm)],[c_66,c_183])).

tff(c_8803,plain,(
    ! [B_749,A_750] :
      ( r1_tarski(k1_relat_1(B_749),A_750)
      | ~ v4_relat_1(B_749,A_750)
      | ~ v1_relat_1(B_749) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_8811,plain,(
    ! [A_17,A_750] :
      ( r1_tarski(A_17,A_750)
      | ~ v4_relat_1(k6_partfun1(A_17),A_750)
      | ~ v1_relat_1(k6_partfun1(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_8803])).

tff(c_8815,plain,(
    ! [A_17,A_750] :
      ( r1_tarski(A_17,A_750)
      | ~ v4_relat_1(k6_partfun1(A_17),A_750) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_8811])).

tff(c_9370,plain,(
    ! [A_810,B_811,A_750] :
      ( r1_tarski(k2_zfmisc_1(A_810,B_811),A_750)
      | ~ v4_relat_1('#skF_4',A_750)
      | ~ v1_xboole_0(B_811) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9331,c_8815])).

tff(c_9554,plain,(
    ! [A_825,B_826,A_827] :
      ( r1_tarski(k2_zfmisc_1(A_825,B_826),A_827)
      | ~ v1_xboole_0(B_826) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8989,c_9370])).

tff(c_9562,plain,(
    ! [A_827] :
      ( r1_tarski('#skF_4',A_827)
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8678,c_9554])).

tff(c_9566,plain,(
    ! [A_828] : r1_tarski('#skF_4',A_828) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8683,c_9562])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( B_6 = A_5
      | ~ r1_tarski(B_6,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_9579,plain,(
    ! [A_832] :
      ( A_832 = '#skF_4'
      | ~ r1_tarski(A_832,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_9566,c_8])).

tff(c_11104,plain,(
    ! [B_926] :
      ( k1_relat_1(B_926) = '#skF_4'
      | ~ v4_relat_1(B_926,'#skF_4')
      | ~ v1_relat_1(B_926) ) ),
    inference(resolution,[status(thm)],[c_22,c_9579])).

tff(c_11127,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_5542,c_11104])).

tff(c_11143,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_11127])).

tff(c_11145,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8802,c_11143])).

tff(c_11146,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_8801])).

tff(c_11153,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11146,c_126])).

tff(c_11159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8766,c_11153])).

tff(c_11160,plain,(
    ~ v2_funct_2('#skF_7','#skF_4') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_11211,plain,(
    ! [C_939,A_940,B_941] :
      ( v1_relat_1(C_939)
      | ~ m1_subset_1(C_939,k1_zfmisc_1(k2_zfmisc_1(A_940,B_941))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_11224,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_80,c_11211])).

tff(c_11475,plain,(
    ! [C_976,B_977,A_978] :
      ( v5_relat_1(C_976,B_977)
      | ~ m1_subset_1(C_976,k1_zfmisc_1(k2_zfmisc_1(A_978,B_977))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_11489,plain,(
    v5_relat_1('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_11475])).

tff(c_11719,plain,(
    ! [A_998,B_999,D_1000] :
      ( r2_relset_1(A_998,B_999,D_1000,D_1000)
      | ~ m1_subset_1(D_1000,k1_zfmisc_1(k2_zfmisc_1(A_998,B_999))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_11730,plain,(
    ! [A_47] : r2_relset_1(A_47,A_47,k6_partfun1(A_47),k6_partfun1(A_47)) ),
    inference(resolution,[status(thm)],[c_66,c_11719])).

tff(c_11980,plain,(
    ! [A_1015,B_1016,C_1017] :
      ( k2_relset_1(A_1015,B_1016,C_1017) = k2_relat_1(C_1017)
      | ~ m1_subset_1(C_1017,k1_zfmisc_1(k2_zfmisc_1(A_1015,B_1016))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_11998,plain,(
    k2_relset_1('#skF_5','#skF_4','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_80,c_11980])).

tff(c_12087,plain,(
    ! [D_1029,C_1030,A_1031,B_1032] :
      ( D_1029 = C_1030
      | ~ r2_relset_1(A_1031,B_1032,C_1030,D_1029)
      | ~ m1_subset_1(D_1029,k1_zfmisc_1(k2_zfmisc_1(A_1031,B_1032)))
      | ~ m1_subset_1(C_1030,k1_zfmisc_1(k2_zfmisc_1(A_1031,B_1032))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_12095,plain,
    ( k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7') = k6_partfun1('#skF_4')
    | ~ m1_subset_1(k6_partfun1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
    | ~ m1_subset_1(k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_78,c_12087])).

tff(c_12110,plain,
    ( k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7') = k6_partfun1('#skF_4')
    | ~ m1_subset_1(k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_12095])).

tff(c_12435,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_12110])).

tff(c_13223,plain,
    ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_12435])).

tff(c_13227,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_84,c_80,c_13223])).

tff(c_13228,plain,(
    k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7') = k6_partfun1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_12110])).

tff(c_14774,plain,(
    ! [A_1180,B_1181,C_1182,D_1183] :
      ( k2_relset_1(A_1180,B_1181,C_1182) = B_1181
      | ~ r2_relset_1(B_1181,B_1181,k1_partfun1(B_1181,A_1180,A_1180,B_1181,D_1183,C_1182),k6_partfun1(B_1181))
      | ~ m1_subset_1(D_1183,k1_zfmisc_1(k2_zfmisc_1(B_1181,A_1180)))
      | ~ v1_funct_2(D_1183,B_1181,A_1180)
      | ~ v1_funct_1(D_1183)
      | ~ m1_subset_1(C_1182,k1_zfmisc_1(k2_zfmisc_1(A_1180,B_1181)))
      | ~ v1_funct_2(C_1182,A_1180,B_1181)
      | ~ v1_funct_1(C_1182) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_14780,plain,
    ( k2_relset_1('#skF_5','#skF_4','#skF_7') = '#skF_4'
    | ~ r2_relset_1('#skF_4','#skF_4',k6_partfun1('#skF_4'),k6_partfun1('#skF_4'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
    | ~ v1_funct_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_13228,c_14774])).

tff(c_14797,plain,(
    k2_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_90,c_88,c_86,c_11730,c_11998,c_14780])).

tff(c_56,plain,(
    ! [B_40] :
      ( v2_funct_2(B_40,k2_relat_1(B_40))
      | ~ v5_relat_1(B_40,k2_relat_1(B_40))
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_14803,plain,
    ( v2_funct_2('#skF_7',k2_relat_1('#skF_7'))
    | ~ v5_relat_1('#skF_7','#skF_4')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_14797,c_56])).

tff(c_14807,plain,(
    v2_funct_2('#skF_7','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11224,c_11489,c_14797,c_14803])).

tff(c_14809,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11160,c_14807])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:08:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.24/3.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.31/3.43  
% 9.31/3.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.31/3.43  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3
% 9.31/3.43  
% 9.31/3.43  %Foreground sorts:
% 9.31/3.43  
% 9.31/3.43  
% 9.31/3.43  %Background operators:
% 9.31/3.43  
% 9.31/3.43  
% 9.31/3.43  %Foreground operators:
% 9.31/3.43  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.31/3.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.31/3.43  tff('#skF_2', type, '#skF_2': $i > $i).
% 9.31/3.43  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.31/3.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.31/3.43  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 9.31/3.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.31/3.43  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.31/3.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.31/3.43  tff('#skF_7', type, '#skF_7': $i).
% 9.31/3.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.31/3.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.31/3.43  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.31/3.43  tff('#skF_5', type, '#skF_5': $i).
% 9.31/3.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.31/3.43  tff('#skF_6', type, '#skF_6': $i).
% 9.31/3.43  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 9.31/3.43  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 9.31/3.43  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.31/3.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.31/3.43  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.31/3.43  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.31/3.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.31/3.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.31/3.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.31/3.43  tff('#skF_4', type, '#skF_4': $i).
% 9.31/3.43  tff('#skF_3', type, '#skF_3': $i > $i).
% 9.31/3.43  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.31/3.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.31/3.43  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.31/3.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.31/3.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.31/3.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.31/3.43  
% 9.31/3.46  tff(f_199, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 9.31/3.46  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 9.31/3.46  tff(f_50, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 9.31/3.46  tff(f_57, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 9.31/3.46  tff(f_140, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 9.31/3.46  tff(f_75, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 9.31/3.46  tff(f_138, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 9.31/3.46  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.31/3.46  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 9.31/3.46  tff(f_92, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 9.31/3.46  tff(f_134, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 9.31/3.46  tff(f_114, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 9.31/3.46  tff(f_179, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 9.31/3.46  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.31/3.46  tff(f_46, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 9.31/3.46  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.31/3.46  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 9.31/3.46  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.31/3.46  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.31/3.46  tff(f_157, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 9.31/3.46  tff(f_122, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 9.31/3.46  tff(c_76, plain, (~v2_funct_2('#skF_7', '#skF_4') | ~v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_199])).
% 9.31/3.46  tff(c_126, plain, (~v2_funct_1('#skF_6')), inference(splitLeft, [status(thm)], [c_76])).
% 9.31/3.46  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.31/3.46  tff(c_16, plain, (![A_9, B_10]: (v1_xboole_0(k2_zfmisc_1(A_9, B_10)) | ~v1_xboole_0(B_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.31/3.46  tff(c_80, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_199])).
% 9.31/3.46  tff(c_256, plain, (![C_88, B_89, A_90]: (~v1_xboole_0(C_88) | ~m1_subset_1(B_89, k1_zfmisc_1(C_88)) | ~r2_hidden(A_90, B_89))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.31/3.46  tff(c_264, plain, (![A_90]: (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_4')) | ~r2_hidden(A_90, '#skF_7'))), inference(resolution, [status(thm)], [c_80, c_256])).
% 9.31/3.46  tff(c_319, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_4'))), inference(splitLeft, [status(thm)], [c_264])).
% 9.31/3.46  tff(c_323, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_16, c_319])).
% 9.31/3.46  tff(c_68, plain, (![A_48]: (k6_relat_1(A_48)=k6_partfun1(A_48))), inference(cnfTransformation, [status(thm)], [f_140])).
% 9.31/3.46  tff(c_28, plain, (![A_17]: (k1_relat_1(k6_relat_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.31/3.46  tff(c_93, plain, (![A_17]: (k1_relat_1(k6_partfun1(A_17))=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_68, c_28])).
% 9.31/3.46  tff(c_66, plain, (![A_47]: (m1_subset_1(k6_partfun1(A_47), k1_zfmisc_1(k2_zfmisc_1(A_47, A_47))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 9.31/3.46  tff(c_183, plain, (![C_83, A_84, B_85]: (v1_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.31/3.46  tff(c_214, plain, (![A_86]: (v1_relat_1(k6_partfun1(A_86)))), inference(resolution, [status(thm)], [c_66, c_183])).
% 9.31/3.46  tff(c_26, plain, (![A_16]: (k1_relat_1(A_16)!=k1_xboole_0 | k1_xboole_0=A_16 | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.31/3.46  tff(c_217, plain, (![A_86]: (k1_relat_1(k6_partfun1(A_86))!=k1_xboole_0 | k6_partfun1(A_86)=k1_xboole_0)), inference(resolution, [status(thm)], [c_214, c_26])).
% 9.31/3.46  tff(c_228, plain, (![A_87]: (k1_xboole_0!=A_87 | k6_partfun1(A_87)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_93, c_217])).
% 9.31/3.46  tff(c_78, plain, (r2_relset_1('#skF_4', '#skF_4', k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7'), k6_partfun1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_199])).
% 9.31/3.46  tff(c_236, plain, (r2_relset_1('#skF_4', '#skF_4', k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7'), k1_xboole_0) | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_228, c_78])).
% 9.31/3.46  tff(c_347, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_236])).
% 9.31/3.46  tff(c_90, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_199])).
% 9.31/3.46  tff(c_88, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_199])).
% 9.31/3.46  tff(c_86, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_199])).
% 9.31/3.46  tff(c_84, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_199])).
% 9.31/3.46  tff(c_82, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_199])).
% 9.31/3.46  tff(c_42, plain, (![A_25]: (v2_funct_1(k6_relat_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.31/3.46  tff(c_91, plain, (![A_25]: (v2_funct_1(k6_partfun1(A_25)))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_42])).
% 9.31/3.46  tff(c_60, plain, (![D_44, F_46, C_43, A_41, B_42, E_45]: (m1_subset_1(k1_partfun1(A_41, B_42, C_43, D_44, E_45, F_46), k1_zfmisc_1(k2_zfmisc_1(A_41, D_44))) | ~m1_subset_1(F_46, k1_zfmisc_1(k2_zfmisc_1(C_43, D_44))) | ~v1_funct_1(F_46) | ~m1_subset_1(E_45, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))) | ~v1_funct_1(E_45))), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.31/3.46  tff(c_1003, plain, (![D_160, C_161, A_162, B_163]: (D_160=C_161 | ~r2_relset_1(A_162, B_163, C_161, D_160) | ~m1_subset_1(D_160, k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.31/3.46  tff(c_1011, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7')=k6_partfun1('#skF_4') | ~m1_subset_1(k6_partfun1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~m1_subset_1(k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(resolution, [status(thm)], [c_78, c_1003])).
% 9.31/3.46  tff(c_1026, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7')=k6_partfun1('#skF_4') | ~m1_subset_1(k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1011])).
% 9.31/3.46  tff(c_1291, plain, (~m1_subset_1(k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(splitLeft, [status(thm)], [c_1026])).
% 9.31/3.46  tff(c_1953, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_60, c_1291])).
% 9.31/3.46  tff(c_1957, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_84, c_80, c_1953])).
% 9.31/3.46  tff(c_1958, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7')=k6_partfun1('#skF_4')), inference(splitRight, [status(thm)], [c_1026])).
% 9.31/3.46  tff(c_2871, plain, (![A_296, E_299, B_297, C_295, D_298]: (k1_xboole_0=C_295 | v2_funct_1(D_298) | ~v2_funct_1(k1_partfun1(A_296, B_297, B_297, C_295, D_298, E_299)) | ~m1_subset_1(E_299, k1_zfmisc_1(k2_zfmisc_1(B_297, C_295))) | ~v1_funct_2(E_299, B_297, C_295) | ~v1_funct_1(E_299) | ~m1_subset_1(D_298, k1_zfmisc_1(k2_zfmisc_1(A_296, B_297))) | ~v1_funct_2(D_298, A_296, B_297) | ~v1_funct_1(D_298))), inference(cnfTransformation, [status(thm)], [f_179])).
% 9.31/3.46  tff(c_2873, plain, (k1_xboole_0='#skF_4' | v2_funct_1('#skF_6') | ~v2_funct_1(k6_partfun1('#skF_4')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1958, c_2871])).
% 9.31/3.46  tff(c_2878, plain, (k1_xboole_0='#skF_4' | v2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_84, c_82, c_80, c_91, c_2873])).
% 9.31/3.46  tff(c_2880, plain, $false, inference(negUnitSimplification, [status(thm)], [c_126, c_347, c_2878])).
% 9.31/3.46  tff(c_2882, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_236])).
% 9.31/3.46  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.31/3.46  tff(c_2896, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2882, c_6])).
% 9.31/3.46  tff(c_2898, plain, $false, inference(negUnitSimplification, [status(thm)], [c_323, c_2896])).
% 9.31/3.46  tff(c_2901, plain, (![A_300]: (~r2_hidden(A_300, '#skF_7'))), inference(splitRight, [status(thm)], [c_264])).
% 9.31/3.46  tff(c_2906, plain, (v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_4, c_2901])).
% 9.31/3.46  tff(c_127, plain, (![B_69, A_70]: (~v1_xboole_0(B_69) | B_69=A_70 | ~v1_xboole_0(A_70))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.31/3.46  tff(c_130, plain, (![A_70]: (k1_xboole_0=A_70 | ~v1_xboole_0(A_70))), inference(resolution, [status(thm)], [c_6, c_127])).
% 9.31/3.46  tff(c_2915, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_2906, c_130])).
% 9.31/3.46  tff(c_30, plain, (![A_17]: (k2_relat_1(k6_relat_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.31/3.46  tff(c_92, plain, (![A_17]: (k2_relat_1(k6_partfun1(A_17))=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_68, c_30])).
% 9.31/3.46  tff(c_248, plain, (![A_87]: (k2_relat_1(k1_xboole_0)=A_87 | k1_xboole_0!=A_87)), inference(superposition, [status(thm), theory('equality')], [c_228, c_92])).
% 9.31/3.46  tff(c_3073, plain, (k2_relat_1('#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_2915, c_2915, c_248])).
% 9.31/3.46  tff(c_196, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_80, c_183])).
% 9.31/3.46  tff(c_24, plain, (![A_16]: (k2_relat_1(A_16)!=k1_xboole_0 | k1_xboole_0=A_16 | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.31/3.46  tff(c_205, plain, (k2_relat_1('#skF_7')!=k1_xboole_0 | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_196, c_24])).
% 9.31/3.46  tff(c_225, plain, (k2_relat_1('#skF_7')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_205])).
% 9.31/3.46  tff(c_2921, plain, (k2_relat_1('#skF_7')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_2915, c_225])).
% 9.31/3.46  tff(c_3076, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3073, c_2921])).
% 9.31/3.46  tff(c_3077, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_205])).
% 9.31/3.46  tff(c_220, plain, (![A_86]: (k2_relat_1(k6_partfun1(A_86))!=k1_xboole_0 | k6_partfun1(A_86)=k1_xboole_0)), inference(resolution, [status(thm)], [c_214, c_24])).
% 9.31/3.46  tff(c_224, plain, (![A_86]: (k1_xboole_0!=A_86 | k6_partfun1(A_86)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_92, c_220])).
% 9.31/3.46  tff(c_5546, plain, (![A_515]: (A_515!='#skF_7' | k6_partfun1(A_515)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3077, c_3077, c_224])).
% 9.31/3.46  tff(c_5557, plain, (r2_relset_1('#skF_4', '#skF_4', k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7'), '#skF_7') | '#skF_7'!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_5546, c_78])).
% 9.31/3.46  tff(c_5579, plain, ('#skF_7'!='#skF_4'), inference(splitLeft, [status(thm)], [c_5557])).
% 9.31/3.46  tff(c_3093, plain, (![C_310, B_311, A_312]: (~v1_xboole_0(C_310) | ~m1_subset_1(B_311, k1_zfmisc_1(C_310)) | ~r2_hidden(A_312, B_311))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.31/3.46  tff(c_3101, plain, (![A_312]: (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_4')) | ~r2_hidden(A_312, '#skF_7'))), inference(resolution, [status(thm)], [c_80, c_3093])).
% 9.31/3.46  tff(c_3118, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_4'))), inference(splitLeft, [status(thm)], [c_3101])).
% 9.31/3.46  tff(c_3122, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_16, c_3118])).
% 9.31/3.46  tff(c_3155, plain, (![A_317]: (A_317!='#skF_7' | k6_partfun1(A_317)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3077, c_3077, c_224])).
% 9.31/3.46  tff(c_3163, plain, (r2_relset_1('#skF_4', '#skF_4', k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7'), '#skF_7') | '#skF_7'!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3155, c_78])).
% 9.31/3.46  tff(c_3265, plain, ('#skF_7'!='#skF_4'), inference(splitLeft, [status(thm)], [c_3163])).
% 9.31/3.46  tff(c_3690, plain, (![D_377, C_378, A_379, B_380]: (D_377=C_378 | ~r2_relset_1(A_379, B_380, C_378, D_377) | ~m1_subset_1(D_377, k1_zfmisc_1(k2_zfmisc_1(A_379, B_380))) | ~m1_subset_1(C_378, k1_zfmisc_1(k2_zfmisc_1(A_379, B_380))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.31/3.46  tff(c_3696, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7')=k6_partfun1('#skF_4') | ~m1_subset_1(k6_partfun1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~m1_subset_1(k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(resolution, [status(thm)], [c_78, c_3690])).
% 9.31/3.46  tff(c_3707, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7')=k6_partfun1('#skF_4') | ~m1_subset_1(k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_3696])).
% 9.31/3.46  tff(c_3977, plain, (~m1_subset_1(k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(splitLeft, [status(thm)], [c_3707])).
% 9.31/3.46  tff(c_4678, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_60, c_3977])).
% 9.31/3.46  tff(c_4682, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_84, c_80, c_4678])).
% 9.31/3.46  tff(c_4683, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7')=k6_partfun1('#skF_4')), inference(splitRight, [status(thm)], [c_3707])).
% 9.31/3.46  tff(c_74, plain, (![C_56, E_59, D_57, B_55, A_54]: (k1_xboole_0=C_56 | v2_funct_1(D_57) | ~v2_funct_1(k1_partfun1(A_54, B_55, B_55, C_56, D_57, E_59)) | ~m1_subset_1(E_59, k1_zfmisc_1(k2_zfmisc_1(B_55, C_56))) | ~v1_funct_2(E_59, B_55, C_56) | ~v1_funct_1(E_59) | ~m1_subset_1(D_57, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))) | ~v1_funct_2(D_57, A_54, B_55) | ~v1_funct_1(D_57))), inference(cnfTransformation, [status(thm)], [f_179])).
% 9.31/3.46  tff(c_5438, plain, (![D_507, E_508, A_505, C_504, B_506]: (C_504='#skF_7' | v2_funct_1(D_507) | ~v2_funct_1(k1_partfun1(A_505, B_506, B_506, C_504, D_507, E_508)) | ~m1_subset_1(E_508, k1_zfmisc_1(k2_zfmisc_1(B_506, C_504))) | ~v1_funct_2(E_508, B_506, C_504) | ~v1_funct_1(E_508) | ~m1_subset_1(D_507, k1_zfmisc_1(k2_zfmisc_1(A_505, B_506))) | ~v1_funct_2(D_507, A_505, B_506) | ~v1_funct_1(D_507))), inference(demodulation, [status(thm), theory('equality')], [c_3077, c_74])).
% 9.31/3.46  tff(c_5440, plain, ('#skF_7'='#skF_4' | v2_funct_1('#skF_6') | ~v2_funct_1(k6_partfun1('#skF_4')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_4683, c_5438])).
% 9.31/3.46  tff(c_5445, plain, ('#skF_7'='#skF_4' | v2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_84, c_82, c_80, c_91, c_5440])).
% 9.31/3.46  tff(c_5447, plain, $false, inference(negUnitSimplification, [status(thm)], [c_126, c_3265, c_5445])).
% 9.31/3.46  tff(c_5449, plain, ('#skF_7'='#skF_4'), inference(splitRight, [status(thm)], [c_3163])).
% 9.31/3.46  tff(c_3085, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3077, c_6])).
% 9.31/3.46  tff(c_5462, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5449, c_3085])).
% 9.31/3.46  tff(c_5470, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3122, c_5462])).
% 9.31/3.46  tff(c_5472, plain, (v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_4'))), inference(splitRight, [status(thm)], [c_3101])).
% 9.31/3.46  tff(c_3084, plain, (![A_70]: (A_70='#skF_7' | ~v1_xboole_0(A_70))), inference(demodulation, [status(thm), theory('equality')], [c_3077, c_130])).
% 9.31/3.46  tff(c_5485, plain, (k2_zfmisc_1('#skF_5', '#skF_4')='#skF_7'), inference(resolution, [status(thm)], [c_5472, c_3084])).
% 9.31/3.46  tff(c_5493, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_5485, c_80])).
% 9.31/3.46  tff(c_7186, plain, (![C_647, F_649, E_645, D_648, B_650, A_646]: (m1_subset_1(k1_partfun1(A_646, B_650, C_647, D_648, E_645, F_649), k1_zfmisc_1(k2_zfmisc_1(A_646, D_648))) | ~m1_subset_1(F_649, k1_zfmisc_1(k2_zfmisc_1(C_647, D_648))) | ~v1_funct_1(F_649) | ~m1_subset_1(E_645, k1_zfmisc_1(k2_zfmisc_1(A_646, B_650))) | ~v1_funct_1(E_645))), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.31/3.46  tff(c_6416, plain, (![D_596, C_597, A_598, B_599]: (D_596=C_597 | ~r2_relset_1(A_598, B_599, C_597, D_596) | ~m1_subset_1(D_596, k1_zfmisc_1(k2_zfmisc_1(A_598, B_599))) | ~m1_subset_1(C_597, k1_zfmisc_1(k2_zfmisc_1(A_598, B_599))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.31/3.46  tff(c_6424, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7')=k6_partfun1('#skF_4') | ~m1_subset_1(k6_partfun1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~m1_subset_1(k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(resolution, [status(thm)], [c_78, c_6416])).
% 9.31/3.46  tff(c_6439, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7')=k6_partfun1('#skF_4') | ~m1_subset_1(k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_6424])).
% 9.31/3.46  tff(c_6625, plain, (~m1_subset_1(k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(splitLeft, [status(thm)], [c_6439])).
% 9.31/3.46  tff(c_7194, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_7186, c_6625])).
% 9.31/3.46  tff(c_7228, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_84, c_5493, c_5485, c_7194])).
% 9.31/3.46  tff(c_7229, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7')=k6_partfun1('#skF_4')), inference(splitRight, [status(thm)], [c_6439])).
% 9.31/3.46  tff(c_8664, plain, (![C_738, A_739, D_741, B_740, E_742]: (C_738='#skF_7' | v2_funct_1(D_741) | ~v2_funct_1(k1_partfun1(A_739, B_740, B_740, C_738, D_741, E_742)) | ~m1_subset_1(E_742, k1_zfmisc_1(k2_zfmisc_1(B_740, C_738))) | ~v1_funct_2(E_742, B_740, C_738) | ~v1_funct_1(E_742) | ~m1_subset_1(D_741, k1_zfmisc_1(k2_zfmisc_1(A_739, B_740))) | ~v1_funct_2(D_741, A_739, B_740) | ~v1_funct_1(D_741))), inference(demodulation, [status(thm), theory('equality')], [c_3077, c_74])).
% 9.31/3.46  tff(c_8666, plain, ('#skF_7'='#skF_4' | v2_funct_1('#skF_6') | ~v2_funct_1(k6_partfun1('#skF_4')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_7229, c_8664])).
% 9.31/3.46  tff(c_8671, plain, ('#skF_7'='#skF_4' | v2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_84, c_82, c_5493, c_5485, c_91, c_8666])).
% 9.31/3.46  tff(c_8673, plain, $false, inference(negUnitSimplification, [status(thm)], [c_126, c_5579, c_8671])).
% 9.31/3.46  tff(c_8675, plain, ('#skF_7'='#skF_4'), inference(splitRight, [status(thm)], [c_5557])).
% 9.31/3.46  tff(c_5571, plain, (![A_515]: (v2_funct_1('#skF_7') | A_515!='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_5546, c_91])).
% 9.31/3.46  tff(c_8758, plain, (![A_515]: (v2_funct_1('#skF_4') | A_515!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8675, c_8675, c_5571])).
% 9.31/3.46  tff(c_8759, plain, (![A_515]: (A_515!='#skF_4')), inference(splitLeft, [status(thm)], [c_8758])).
% 9.31/3.46  tff(c_135, plain, (![A_73]: (k1_xboole_0=A_73 | ~v1_xboole_0(A_73))), inference(resolution, [status(thm)], [c_6, c_127])).
% 9.31/3.46  tff(c_150, plain, (![A_75, B_76]: (k2_zfmisc_1(A_75, B_76)=k1_xboole_0 | ~v1_xboole_0(B_76))), inference(resolution, [status(thm)], [c_16, c_135])).
% 9.31/3.46  tff(c_156, plain, (![A_75]: (k2_zfmisc_1(A_75, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_150])).
% 9.31/3.46  tff(c_3082, plain, (![A_75]: (k2_zfmisc_1(A_75, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3077, c_3077, c_156])).
% 9.31/3.46  tff(c_8678, plain, (![A_75]: (k2_zfmisc_1(A_75, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8675, c_8675, c_3082])).
% 9.31/3.46  tff(c_8765, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8759, c_8678])).
% 9.31/3.46  tff(c_8766, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_8758])).
% 9.31/3.46  tff(c_8684, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8675, c_3077])).
% 9.31/3.46  tff(c_197, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_86, c_183])).
% 9.31/3.46  tff(c_212, plain, (k1_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_197, c_26])).
% 9.31/3.46  tff(c_8801, plain, (k1_relat_1('#skF_6')!='#skF_4' | '#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8684, c_8684, c_212])).
% 9.31/3.46  tff(c_8802, plain, (k1_relat_1('#skF_6')!='#skF_4'), inference(splitLeft, [status(thm)], [c_8801])).
% 9.31/3.46  tff(c_5528, plain, (![C_511, A_512, B_513]: (v4_relat_1(C_511, A_512) | ~m1_subset_1(C_511, k1_zfmisc_1(k2_zfmisc_1(A_512, B_513))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.31/3.46  tff(c_5542, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_86, c_5528])).
% 9.31/3.46  tff(c_22, plain, (![B_15, A_14]: (r1_tarski(k1_relat_1(B_15), A_14) | ~v4_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.31/3.46  tff(c_8683, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8675, c_3085])).
% 9.31/3.46  tff(c_8677, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_8675, c_8675, c_5493])).
% 9.31/3.46  tff(c_5531, plain, (![C_511, A_75]: (v4_relat_1(C_511, A_75) | ~m1_subset_1(C_511, k1_zfmisc_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_3082, c_5528])).
% 9.31/3.46  tff(c_8986, plain, (![C_774, A_775]: (v4_relat_1(C_774, A_775) | ~m1_subset_1(C_774, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_8675, c_5531])).
% 9.31/3.46  tff(c_8989, plain, (![A_775]: (v4_relat_1('#skF_4', A_775))), inference(resolution, [status(thm)], [c_8677, c_8986])).
% 9.31/3.46  tff(c_9006, plain, (![A_781, A_782]: (~v1_xboole_0(k2_zfmisc_1(A_781, A_781)) | ~r2_hidden(A_782, k6_partfun1(A_781)))), inference(resolution, [status(thm)], [c_66, c_3093])).
% 9.31/3.46  tff(c_9016, plain, (![A_783, B_784]: (~r2_hidden(A_783, k6_partfun1(B_784)) | ~v1_xboole_0(B_784))), inference(resolution, [status(thm)], [c_16, c_9006])).
% 9.31/3.46  tff(c_9034, plain, (![B_788]: (~v1_xboole_0(B_788) | v1_xboole_0(k6_partfun1(B_788)))), inference(resolution, [status(thm)], [c_4, c_9016])).
% 9.31/3.46  tff(c_8681, plain, (![A_70]: (A_70='#skF_4' | ~v1_xboole_0(A_70))), inference(demodulation, [status(thm), theory('equality')], [c_8675, c_3084])).
% 9.31/3.46  tff(c_9052, plain, (![B_789]: (k6_partfun1(B_789)='#skF_4' | ~v1_xboole_0(B_789))), inference(resolution, [status(thm)], [c_9034, c_8681])).
% 9.31/3.46  tff(c_9331, plain, (![A_810, B_811]: (k6_partfun1(k2_zfmisc_1(A_810, B_811))='#skF_4' | ~v1_xboole_0(B_811))), inference(resolution, [status(thm)], [c_16, c_9052])).
% 9.31/3.46  tff(c_195, plain, (![A_47]: (v1_relat_1(k6_partfun1(A_47)))), inference(resolution, [status(thm)], [c_66, c_183])).
% 9.31/3.46  tff(c_8803, plain, (![B_749, A_750]: (r1_tarski(k1_relat_1(B_749), A_750) | ~v4_relat_1(B_749, A_750) | ~v1_relat_1(B_749))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.31/3.46  tff(c_8811, plain, (![A_17, A_750]: (r1_tarski(A_17, A_750) | ~v4_relat_1(k6_partfun1(A_17), A_750) | ~v1_relat_1(k6_partfun1(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_93, c_8803])).
% 9.31/3.46  tff(c_8815, plain, (![A_17, A_750]: (r1_tarski(A_17, A_750) | ~v4_relat_1(k6_partfun1(A_17), A_750))), inference(demodulation, [status(thm), theory('equality')], [c_195, c_8811])).
% 9.31/3.46  tff(c_9370, plain, (![A_810, B_811, A_750]: (r1_tarski(k2_zfmisc_1(A_810, B_811), A_750) | ~v4_relat_1('#skF_4', A_750) | ~v1_xboole_0(B_811))), inference(superposition, [status(thm), theory('equality')], [c_9331, c_8815])).
% 9.31/3.46  tff(c_9554, plain, (![A_825, B_826, A_827]: (r1_tarski(k2_zfmisc_1(A_825, B_826), A_827) | ~v1_xboole_0(B_826))), inference(demodulation, [status(thm), theory('equality')], [c_8989, c_9370])).
% 9.31/3.46  tff(c_9562, plain, (![A_827]: (r1_tarski('#skF_4', A_827) | ~v1_xboole_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8678, c_9554])).
% 9.31/3.46  tff(c_9566, plain, (![A_828]: (r1_tarski('#skF_4', A_828))), inference(demodulation, [status(thm), theory('equality')], [c_8683, c_9562])).
% 9.31/3.46  tff(c_8, plain, (![B_6, A_5]: (B_6=A_5 | ~r1_tarski(B_6, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.31/3.46  tff(c_9579, plain, (![A_832]: (A_832='#skF_4' | ~r1_tarski(A_832, '#skF_4'))), inference(resolution, [status(thm)], [c_9566, c_8])).
% 9.31/3.46  tff(c_11104, plain, (![B_926]: (k1_relat_1(B_926)='#skF_4' | ~v4_relat_1(B_926, '#skF_4') | ~v1_relat_1(B_926))), inference(resolution, [status(thm)], [c_22, c_9579])).
% 9.31/3.46  tff(c_11127, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_5542, c_11104])).
% 9.31/3.46  tff(c_11143, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_197, c_11127])).
% 9.31/3.46  tff(c_11145, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8802, c_11143])).
% 9.31/3.46  tff(c_11146, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_8801])).
% 9.31/3.46  tff(c_11153, plain, (~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11146, c_126])).
% 9.31/3.46  tff(c_11159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8766, c_11153])).
% 9.31/3.46  tff(c_11160, plain, (~v2_funct_2('#skF_7', '#skF_4')), inference(splitRight, [status(thm)], [c_76])).
% 9.31/3.46  tff(c_11211, plain, (![C_939, A_940, B_941]: (v1_relat_1(C_939) | ~m1_subset_1(C_939, k1_zfmisc_1(k2_zfmisc_1(A_940, B_941))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.31/3.46  tff(c_11224, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_80, c_11211])).
% 9.31/3.46  tff(c_11475, plain, (![C_976, B_977, A_978]: (v5_relat_1(C_976, B_977) | ~m1_subset_1(C_976, k1_zfmisc_1(k2_zfmisc_1(A_978, B_977))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.31/3.46  tff(c_11489, plain, (v5_relat_1('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_80, c_11475])).
% 9.31/3.46  tff(c_11719, plain, (![A_998, B_999, D_1000]: (r2_relset_1(A_998, B_999, D_1000, D_1000) | ~m1_subset_1(D_1000, k1_zfmisc_1(k2_zfmisc_1(A_998, B_999))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.31/3.46  tff(c_11730, plain, (![A_47]: (r2_relset_1(A_47, A_47, k6_partfun1(A_47), k6_partfun1(A_47)))), inference(resolution, [status(thm)], [c_66, c_11719])).
% 9.31/3.46  tff(c_11980, plain, (![A_1015, B_1016, C_1017]: (k2_relset_1(A_1015, B_1016, C_1017)=k2_relat_1(C_1017) | ~m1_subset_1(C_1017, k1_zfmisc_1(k2_zfmisc_1(A_1015, B_1016))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.31/3.46  tff(c_11998, plain, (k2_relset_1('#skF_5', '#skF_4', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_80, c_11980])).
% 9.31/3.46  tff(c_12087, plain, (![D_1029, C_1030, A_1031, B_1032]: (D_1029=C_1030 | ~r2_relset_1(A_1031, B_1032, C_1030, D_1029) | ~m1_subset_1(D_1029, k1_zfmisc_1(k2_zfmisc_1(A_1031, B_1032))) | ~m1_subset_1(C_1030, k1_zfmisc_1(k2_zfmisc_1(A_1031, B_1032))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.31/3.46  tff(c_12095, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7')=k6_partfun1('#skF_4') | ~m1_subset_1(k6_partfun1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~m1_subset_1(k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(resolution, [status(thm)], [c_78, c_12087])).
% 9.31/3.46  tff(c_12110, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7')=k6_partfun1('#skF_4') | ~m1_subset_1(k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_12095])).
% 9.31/3.46  tff(c_12435, plain, (~m1_subset_1(k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(splitLeft, [status(thm)], [c_12110])).
% 9.31/3.46  tff(c_13223, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_60, c_12435])).
% 9.31/3.46  tff(c_13227, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_84, c_80, c_13223])).
% 9.31/3.46  tff(c_13228, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7')=k6_partfun1('#skF_4')), inference(splitRight, [status(thm)], [c_12110])).
% 9.31/3.46  tff(c_14774, plain, (![A_1180, B_1181, C_1182, D_1183]: (k2_relset_1(A_1180, B_1181, C_1182)=B_1181 | ~r2_relset_1(B_1181, B_1181, k1_partfun1(B_1181, A_1180, A_1180, B_1181, D_1183, C_1182), k6_partfun1(B_1181)) | ~m1_subset_1(D_1183, k1_zfmisc_1(k2_zfmisc_1(B_1181, A_1180))) | ~v1_funct_2(D_1183, B_1181, A_1180) | ~v1_funct_1(D_1183) | ~m1_subset_1(C_1182, k1_zfmisc_1(k2_zfmisc_1(A_1180, B_1181))) | ~v1_funct_2(C_1182, A_1180, B_1181) | ~v1_funct_1(C_1182))), inference(cnfTransformation, [status(thm)], [f_157])).
% 9.31/3.46  tff(c_14780, plain, (k2_relset_1('#skF_5', '#skF_4', '#skF_7')='#skF_4' | ~r2_relset_1('#skF_4', '#skF_4', k6_partfun1('#skF_4'), k6_partfun1('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_13228, c_14774])).
% 9.31/3.46  tff(c_14797, plain, (k2_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_90, c_88, c_86, c_11730, c_11998, c_14780])).
% 9.31/3.46  tff(c_56, plain, (![B_40]: (v2_funct_2(B_40, k2_relat_1(B_40)) | ~v5_relat_1(B_40, k2_relat_1(B_40)) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_122])).
% 9.31/3.46  tff(c_14803, plain, (v2_funct_2('#skF_7', k2_relat_1('#skF_7')) | ~v5_relat_1('#skF_7', '#skF_4') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_14797, c_56])).
% 9.31/3.46  tff(c_14807, plain, (v2_funct_2('#skF_7', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11224, c_11489, c_14797, c_14803])).
% 9.31/3.46  tff(c_14809, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11160, c_14807])).
% 9.31/3.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.31/3.46  
% 9.31/3.46  Inference rules
% 9.31/3.46  ----------------------
% 9.31/3.46  #Ref     : 40
% 9.31/3.46  #Sup     : 3486
% 9.31/3.46  #Fact    : 0
% 9.31/3.46  #Define  : 0
% 9.31/3.46  #Split   : 48
% 9.31/3.46  #Chain   : 0
% 9.31/3.46  #Close   : 0
% 9.31/3.46  
% 9.31/3.46  Ordering : KBO
% 9.31/3.46  
% 9.31/3.46  Simplification rules
% 9.31/3.46  ----------------------
% 9.31/3.46  #Subsume      : 531
% 9.31/3.46  #Demod        : 2837
% 9.31/3.46  #Tautology    : 1844
% 9.31/3.46  #SimpNegUnit  : 50
% 9.31/3.46  #BackRed      : 111
% 9.31/3.46  
% 9.31/3.46  #Partial instantiations: 0
% 9.31/3.46  #Strategies tried      : 1
% 9.31/3.46  
% 9.31/3.46  Timing (in seconds)
% 9.31/3.46  ----------------------
% 9.31/3.46  Preprocessing        : 0.37
% 9.31/3.46  Parsing              : 0.20
% 9.31/3.46  CNF conversion       : 0.03
% 9.31/3.46  Main loop            : 2.18
% 9.31/3.46  Inferencing          : 0.66
% 9.31/3.46  Reduction            : 0.80
% 9.31/3.46  Demodulation         : 0.58
% 9.31/3.46  BG Simplification    : 0.07
% 9.31/3.46  Subsumption          : 0.48
% 9.31/3.46  Abstraction          : 0.09
% 9.31/3.46  MUC search           : 0.00
% 9.31/3.46  Cooper               : 0.00
% 9.31/3.46  Total                : 2.62
% 9.31/3.46  Index Insertion      : 0.00
% 9.31/3.46  Index Deletion       : 0.00
% 9.31/3.46  Index Matching       : 0.00
% 9.31/3.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
