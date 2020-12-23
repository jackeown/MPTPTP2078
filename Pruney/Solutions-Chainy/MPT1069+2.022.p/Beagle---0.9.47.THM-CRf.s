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
% DateTime   : Thu Dec  3 10:17:48 EST 2020

% Result     : Theorem 30.21s
% Output     : CNFRefutation 30.21s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 450 expanded)
%              Number of leaves         :   48 ( 175 expanded)
%              Depth                    :   21
%              Number of atoms          :  342 (1467 expanded)
%              Number of equality atoms :   73 ( 340 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_202,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_50,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_177,axiom,(
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

tff(f_48,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_142,axiom,(
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

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_153,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_88,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_72,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_84,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_82,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_129,plain,(
    ! [C_92,A_93,B_94] :
      ( v1_relat_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_141,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_129])).

tff(c_86,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_99,plain,(
    ! [B_85,A_86] :
      ( ~ r1_tarski(B_85,A_86)
      | ~ r2_hidden(A_86,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_104,plain,(
    ! [A_87] :
      ( ~ r1_tarski(A_87,'#skF_1'(A_87))
      | v1_xboole_0(A_87) ) ),
    inference(resolution,[status(thm)],[c_4,c_99])).

tff(c_109,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20,c_104])).

tff(c_78,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_329,plain,(
    ! [C_121,A_122,B_123] :
      ( v4_relat_1(C_121,A_122)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_342,plain,(
    v4_relat_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_329])).

tff(c_76,plain,(
    m1_subset_1('#skF_8','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_962,plain,(
    ! [A_190,B_191,C_192] :
      ( k1_relset_1(A_190,B_191,C_192) = k1_relat_1(C_192)
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(A_190,B_191))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_978,plain,(
    k1_relset_1('#skF_5','#skF_3','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_78,c_962])).

tff(c_823,plain,(
    ! [A_180,B_181,C_182] :
      ( k2_relset_1(A_180,B_181,C_182) = k2_relat_1(C_182)
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(A_180,B_181))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_835,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_823])).

tff(c_74,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_917,plain,(
    r1_tarski(k2_relat_1('#skF_6'),k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_835,c_74])).

tff(c_983,plain,(
    r1_tarski(k2_relat_1('#skF_6'),k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_978,c_917])).

tff(c_80,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_2581,plain,(
    ! [F_290,C_289,A_287,B_288,E_291,D_286] :
      ( k1_funct_1(k8_funct_2(B_288,C_289,A_287,D_286,E_291),F_290) = k1_funct_1(E_291,k1_funct_1(D_286,F_290))
      | k1_xboole_0 = B_288
      | ~ r1_tarski(k2_relset_1(B_288,C_289,D_286),k1_relset_1(C_289,A_287,E_291))
      | ~ m1_subset_1(F_290,B_288)
      | ~ m1_subset_1(E_291,k1_zfmisc_1(k2_zfmisc_1(C_289,A_287)))
      | ~ v1_funct_1(E_291)
      | ~ m1_subset_1(D_286,k1_zfmisc_1(k2_zfmisc_1(B_288,C_289)))
      | ~ v1_funct_2(D_286,B_288,C_289)
      | ~ v1_funct_1(D_286)
      | v1_xboole_0(C_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_2589,plain,(
    ! [B_288,D_286,F_290] :
      ( k1_funct_1(k8_funct_2(B_288,'#skF_5','#skF_3',D_286,'#skF_7'),F_290) = k1_funct_1('#skF_7',k1_funct_1(D_286,F_290))
      | k1_xboole_0 = B_288
      | ~ r1_tarski(k2_relset_1(B_288,'#skF_5',D_286),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_290,B_288)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(D_286,k1_zfmisc_1(k2_zfmisc_1(B_288,'#skF_5')))
      | ~ v1_funct_2(D_286,B_288,'#skF_5')
      | ~ v1_funct_1(D_286)
      | v1_xboole_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_978,c_2581])).

tff(c_2604,plain,(
    ! [B_288,D_286,F_290] :
      ( k1_funct_1(k8_funct_2(B_288,'#skF_5','#skF_3',D_286,'#skF_7'),F_290) = k1_funct_1('#skF_7',k1_funct_1(D_286,F_290))
      | k1_xboole_0 = B_288
      | ~ r1_tarski(k2_relset_1(B_288,'#skF_5',D_286),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_290,B_288)
      | ~ m1_subset_1(D_286,k1_zfmisc_1(k2_zfmisc_1(B_288,'#skF_5')))
      | ~ v1_funct_2(D_286,B_288,'#skF_5')
      | ~ v1_funct_1(D_286)
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_2589])).

tff(c_2988,plain,(
    ! [B_318,D_319,F_320] :
      ( k1_funct_1(k8_funct_2(B_318,'#skF_5','#skF_3',D_319,'#skF_7'),F_320) = k1_funct_1('#skF_7',k1_funct_1(D_319,F_320))
      | k1_xboole_0 = B_318
      | ~ r1_tarski(k2_relset_1(B_318,'#skF_5',D_319),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_320,B_318)
      | ~ m1_subset_1(D_319,k1_zfmisc_1(k2_zfmisc_1(B_318,'#skF_5')))
      | ~ v1_funct_2(D_319,B_318,'#skF_5')
      | ~ v1_funct_1(D_319) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_2604])).

tff(c_2993,plain,(
    ! [F_320] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_320) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_320))
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_320,'#skF_4')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_835,c_2988])).

tff(c_3000,plain,(
    ! [F_320] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_320) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_320))
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1(F_320,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_983,c_2993])).

tff(c_3001,plain,(
    ! [F_320] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_320) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_320))
      | ~ m1_subset_1(F_320,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3000])).

tff(c_18,plain,(
    ! [B_12] : r1_tarski(B_12,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_977,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_962])).

tff(c_1993,plain,(
    ! [B_255,A_256,C_257] :
      ( k1_xboole_0 = B_255
      | k1_relset_1(A_256,B_255,C_257) = A_256
      | ~ v1_funct_2(C_257,A_256,B_255)
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(A_256,B_255))) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_2012,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_1993])).

tff(c_2019,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_977,c_2012])).

tff(c_2022,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2019])).

tff(c_28,plain,(
    ! [B_19,A_18] :
      ( v4_relat_1(B_19,A_18)
      | ~ r1_tarski(k1_relat_1(B_19),A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2056,plain,(
    ! [A_18] :
      ( v4_relat_1('#skF_6',A_18)
      | ~ r1_tarski('#skF_4',A_18)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2022,c_28])).

tff(c_2087,plain,(
    ! [A_18] :
      ( v4_relat_1('#skF_6',A_18)
      | ~ r1_tarski('#skF_4',A_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_2056])).

tff(c_702,plain,(
    ! [C_167,A_168,B_169] :
      ( v1_xboole_0(C_167)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_168,B_169)))
      | ~ v1_xboole_0(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_714,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_702])).

tff(c_716,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_714])).

tff(c_30,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k1_relat_1(B_19),A_18)
      | ~ v4_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( r2_hidden(A_14,B_15)
      | v1_xboole_0(B_15)
      | ~ m1_subset_1(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_552,plain,(
    ! [C_153,B_154,A_155] :
      ( r2_hidden(C_153,B_154)
      | ~ r2_hidden(C_153,A_155)
      | ~ r1_tarski(A_155,B_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4155,plain,(
    ! [A_366,B_367,B_368] :
      ( r2_hidden(A_366,B_367)
      | ~ r1_tarski(B_368,B_367)
      | v1_xboole_0(B_368)
      | ~ m1_subset_1(A_366,B_368) ) ),
    inference(resolution,[status(thm)],[c_22,c_552])).

tff(c_22114,plain,(
    ! [A_832,A_833,B_834] :
      ( r2_hidden(A_832,A_833)
      | v1_xboole_0(k1_relat_1(B_834))
      | ~ m1_subset_1(A_832,k1_relat_1(B_834))
      | ~ v4_relat_1(B_834,A_833)
      | ~ v1_relat_1(B_834) ) ),
    inference(resolution,[status(thm)],[c_30,c_4155])).

tff(c_22146,plain,(
    ! [A_832,A_833] :
      ( r2_hidden(A_832,A_833)
      | v1_xboole_0(k1_relat_1('#skF_6'))
      | ~ m1_subset_1(A_832,'#skF_4')
      | ~ v4_relat_1('#skF_6',A_833)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2022,c_22114])).

tff(c_22170,plain,(
    ! [A_832,A_833] :
      ( r2_hidden(A_832,A_833)
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_832,'#skF_4')
      | ~ v4_relat_1('#skF_6',A_833) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_2022,c_22146])).

tff(c_22226,plain,(
    ! [A_835,A_836] :
      ( r2_hidden(A_835,A_836)
      | ~ m1_subset_1(A_835,'#skF_4')
      | ~ v4_relat_1('#skF_6',A_836) ) ),
    inference(negUnitSimplification,[status(thm)],[c_716,c_22170])).

tff(c_22277,plain,(
    ! [A_835,A_18] :
      ( r2_hidden(A_835,A_18)
      | ~ m1_subset_1(A_835,'#skF_4')
      | ~ r1_tarski('#skF_4',A_18) ) ),
    inference(resolution,[status(thm)],[c_2087,c_22226])).

tff(c_467,plain,(
    ! [C_138,B_139,A_140] :
      ( v5_relat_1(C_138,B_139)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_140,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_480,plain,(
    v5_relat_1('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_467])).

tff(c_142,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_78,c_129])).

tff(c_1312,plain,(
    ! [B_219,A_220] :
      ( r2_hidden(k1_funct_1(B_219,A_220),k2_relat_1(B_219))
      | ~ r2_hidden(A_220,k1_relat_1(B_219))
      | ~ v1_funct_1(B_219)
      | ~ v1_relat_1(B_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_7794,plain,(
    ! [B_495,A_496,B_497] :
      ( r2_hidden(k1_funct_1(B_495,A_496),B_497)
      | ~ r1_tarski(k2_relat_1(B_495),B_497)
      | ~ r2_hidden(A_496,k1_relat_1(B_495))
      | ~ v1_funct_1(B_495)
      | ~ v1_relat_1(B_495) ) ),
    inference(resolution,[status(thm)],[c_1312,c_6])).

tff(c_66,plain,(
    ! [A_47,B_48,C_50] :
      ( k7_partfun1(A_47,B_48,C_50) = k1_funct_1(B_48,C_50)
      | ~ r2_hidden(C_50,k1_relat_1(B_48))
      | ~ v1_funct_1(B_48)
      | ~ v5_relat_1(B_48,A_47)
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_30619,plain,(
    ! [A_991,B_992,B_993,A_994] :
      ( k7_partfun1(A_991,B_992,k1_funct_1(B_993,A_994)) = k1_funct_1(B_992,k1_funct_1(B_993,A_994))
      | ~ v1_funct_1(B_992)
      | ~ v5_relat_1(B_992,A_991)
      | ~ v1_relat_1(B_992)
      | ~ r1_tarski(k2_relat_1(B_993),k1_relat_1(B_992))
      | ~ r2_hidden(A_994,k1_relat_1(B_993))
      | ~ v1_funct_1(B_993)
      | ~ v1_relat_1(B_993) ) ),
    inference(resolution,[status(thm)],[c_7794,c_66])).

tff(c_30671,plain,(
    ! [A_991,A_994] :
      ( k7_partfun1(A_991,'#skF_7',k1_funct_1('#skF_6',A_994)) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',A_994))
      | ~ v1_funct_1('#skF_7')
      | ~ v5_relat_1('#skF_7',A_991)
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(A_994,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_983,c_30619])).

tff(c_64058,plain,(
    ! [A_1378,A_1379] :
      ( k7_partfun1(A_1378,'#skF_7',k1_funct_1('#skF_6',A_1379)) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',A_1379))
      | ~ v5_relat_1('#skF_7',A_1378)
      | ~ r2_hidden(A_1379,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_86,c_2022,c_142,c_80,c_30671])).

tff(c_70,plain,(
    k7_partfun1('#skF_3','#skF_7',k1_funct_1('#skF_6','#skF_8')) != k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_64064,plain,
    ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
    | ~ v5_relat_1('#skF_7','#skF_3')
    | ~ r2_hidden('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_64058,c_70])).

tff(c_64070,plain,
    ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
    | ~ r2_hidden('#skF_8','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_64064])).

tff(c_106832,plain,(
    ~ r2_hidden('#skF_8','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_64070])).

tff(c_106835,plain,
    ( ~ m1_subset_1('#skF_8','#skF_4')
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_22277,c_106832])).

tff(c_106845,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_76,c_106835])).

tff(c_106846,plain,(
    k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_64070])).

tff(c_109545,plain,(
    ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3001,c_106846])).

tff(c_109549,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_109545])).

tff(c_109550,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2019])).

tff(c_582,plain,(
    ! [A_159,B_160] :
      ( r2_hidden('#skF_1'(A_159),B_160)
      | ~ r1_tarski(A_159,B_160)
      | v1_xboole_0(A_159) ) ),
    inference(resolution,[status(thm)],[c_4,c_552])).

tff(c_34,plain,(
    ! [B_23,A_22] :
      ( ~ r1_tarski(B_23,A_22)
      | ~ r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_629,plain,(
    ! [B_163,A_164] :
      ( ~ r1_tarski(B_163,'#skF_1'(A_164))
      | ~ r1_tarski(A_164,B_163)
      | v1_xboole_0(A_164) ) ),
    inference(resolution,[status(thm)],[c_582,c_34])).

tff(c_650,plain,(
    ! [A_165] :
      ( ~ r1_tarski(A_165,k1_xboole_0)
      | v1_xboole_0(A_165) ) ),
    inference(resolution,[status(thm)],[c_20,c_629])).

tff(c_667,plain,(
    ! [B_19] :
      ( v1_xboole_0(k1_relat_1(B_19))
      | ~ v4_relat_1(B_19,k1_xboole_0)
      | ~ v1_relat_1(B_19) ) ),
    inference(resolution,[status(thm)],[c_30,c_650])).

tff(c_206,plain,(
    ! [A_105,B_106] :
      ( r2_hidden('#skF_2'(A_105,B_106),A_105)
      | r1_tarski(A_105,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_215,plain,(
    ! [A_107,B_108] :
      ( ~ v1_xboole_0(A_107)
      | r1_tarski(A_107,B_108) ) ),
    inference(resolution,[status(thm)],[c_206,c_2])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( B_12 = A_11
      | ~ r1_tarski(B_12,A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_240,plain,(
    ! [B_110,A_111] :
      ( B_110 = A_111
      | ~ r1_tarski(B_110,A_111)
      | ~ v1_xboole_0(A_111) ) ),
    inference(resolution,[status(thm)],[c_215,c_14])).

tff(c_261,plain,
    ( k2_relset_1('#skF_4','#skF_5','#skF_6') = k1_relset_1('#skF_5','#skF_3','#skF_7')
    | ~ v1_xboole_0(k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(resolution,[status(thm)],[c_74,c_240])).

tff(c_320,plain,(
    ~ v1_xboole_0(k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_261])).

tff(c_984,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_978,c_320])).

tff(c_991,plain,
    ( ~ v4_relat_1('#skF_7',k1_xboole_0)
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_667,c_984])).

tff(c_994,plain,(
    ~ v4_relat_1('#skF_7',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_991])).

tff(c_109569,plain,(
    ~ v4_relat_1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109550,c_994])).

tff(c_109594,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_109569])).

tff(c_109596,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_714])).

tff(c_12,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_109625,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_109596,c_12])).

tff(c_109632,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_109625])).

tff(c_109634,plain,(
    v1_xboole_0(k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_261])).

tff(c_109652,plain,(
    k1_relset_1('#skF_5','#skF_3','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_109634,c_12])).

tff(c_109655,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109652,c_74])).

tff(c_231,plain,(
    ! [B_108,A_107] :
      ( B_108 = A_107
      | ~ r1_tarski(B_108,A_107)
      | ~ v1_xboole_0(A_107) ) ),
    inference(resolution,[status(thm)],[c_215,c_14])).

tff(c_109667,plain,
    ( k2_relset_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_109655,c_231])).

tff(c_109676,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_109667])).

tff(c_110184,plain,(
    ! [A_1758,B_1759,C_1760] :
      ( k2_relset_1(A_1758,B_1759,C_1760) = k2_relat_1(C_1760)
      | ~ m1_subset_1(C_1760,k1_zfmisc_1(k2_zfmisc_1(A_1758,B_1759))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_110194,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_110184])).

tff(c_110200,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_109676,c_110194])).

tff(c_110323,plain,(
    ! [B_1773,A_1774] :
      ( r2_hidden(k1_funct_1(B_1773,A_1774),k2_relat_1(B_1773))
      | ~ r2_hidden(A_1774,k1_relat_1(B_1773))
      | ~ v1_funct_1(B_1773)
      | ~ v1_relat_1(B_1773) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_110334,plain,(
    ! [A_1774] :
      ( r2_hidden(k1_funct_1('#skF_6',A_1774),k1_xboole_0)
      | ~ r2_hidden(A_1774,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110200,c_110323])).

tff(c_110480,plain,(
    ! [A_1790] :
      ( r2_hidden(k1_funct_1('#skF_6',A_1790),k1_xboole_0)
      | ~ r2_hidden(A_1790,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_86,c_110334])).

tff(c_110485,plain,(
    ! [A_1790] :
      ( ~ r1_tarski(k1_xboole_0,k1_funct_1('#skF_6',A_1790))
      | ~ r2_hidden(A_1790,k1_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_110480,c_34])).

tff(c_110498,plain,(
    ! [A_1791] : ~ r2_hidden(A_1791,k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_110485])).

tff(c_110518,plain,(
    v1_xboole_0(k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_4,c_110498])).

tff(c_110544,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_110518,c_12])).

tff(c_110216,plain,(
    ! [A_1762,B_1763,C_1764] :
      ( k1_relset_1(A_1762,B_1763,C_1764) = k1_relat_1(C_1764)
      | ~ m1_subset_1(C_1764,k1_zfmisc_1(k2_zfmisc_1(A_1762,B_1763))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_110231,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_110216])).

tff(c_110557,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_110544,c_110231])).

tff(c_110624,plain,(
    ! [B_1796,A_1797,C_1798] :
      ( k1_xboole_0 = B_1796
      | k1_relset_1(A_1797,B_1796,C_1798) = A_1797
      | ~ v1_funct_2(C_1798,A_1797,B_1796)
      | ~ m1_subset_1(C_1798,k1_zfmisc_1(k2_zfmisc_1(A_1797,B_1796))) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_110637,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_110624])).

tff(c_110644,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_110557,c_110637])).

tff(c_110645,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_110644])).

tff(c_110681,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110645,c_109])).

tff(c_110686,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_110681])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:15:59 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 30.21/20.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 30.21/20.66  
% 30.21/20.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 30.21/20.66  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2
% 30.21/20.66  
% 30.21/20.66  %Foreground sorts:
% 30.21/20.66  
% 30.21/20.66  
% 30.21/20.66  %Background operators:
% 30.21/20.66  
% 30.21/20.66  
% 30.21/20.66  %Foreground operators:
% 30.21/20.66  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 30.21/20.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 30.21/20.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 30.21/20.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 30.21/20.66  tff('#skF_1', type, '#skF_1': $i > $i).
% 30.21/20.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 30.21/20.66  tff('#skF_7', type, '#skF_7': $i).
% 30.21/20.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 30.21/20.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 30.21/20.66  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 30.21/20.66  tff('#skF_5', type, '#skF_5': $i).
% 30.21/20.66  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 30.21/20.66  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 30.21/20.66  tff('#skF_6', type, '#skF_6': $i).
% 30.21/20.66  tff('#skF_3', type, '#skF_3': $i).
% 30.21/20.66  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 30.21/20.66  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 30.21/20.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 30.21/20.66  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 30.21/20.66  tff('#skF_8', type, '#skF_8': $i).
% 30.21/20.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 30.21/20.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 30.21/20.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 30.21/20.66  tff('#skF_4', type, '#skF_4': $i).
% 30.21/20.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 30.21/20.66  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 30.21/20.66  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 30.21/20.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 30.21/20.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 30.21/20.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 30.21/20.66  
% 30.21/20.68  tff(f_202, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 30.21/20.68  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 30.21/20.68  tff(f_50, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 30.21/20.68  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 30.21/20.68  tff(f_79, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 30.21/20.68  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 30.21/20.68  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 30.21/20.68  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 30.21/20.68  tff(f_177, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 30.21/20.68  tff(f_48, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 30.21/20.68  tff(f_142, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 30.21/20.68  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 30.21/20.68  tff(f_96, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 30.21/20.68  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 30.21/20.68  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 30.21/20.68  tff(f_74, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 30.21/20.68  tff(f_153, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 30.21/20.68  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 30.21/20.68  tff(c_88, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_202])).
% 30.21/20.68  tff(c_72, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_202])).
% 30.21/20.68  tff(c_84, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_202])).
% 30.21/20.68  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 30.21/20.68  tff(c_20, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 30.21/20.68  tff(c_82, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_202])).
% 30.21/20.68  tff(c_129, plain, (![C_92, A_93, B_94]: (v1_relat_1(C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 30.21/20.68  tff(c_141, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_82, c_129])).
% 30.21/20.68  tff(c_86, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_202])).
% 30.21/20.68  tff(c_99, plain, (![B_85, A_86]: (~r1_tarski(B_85, A_86) | ~r2_hidden(A_86, B_85))), inference(cnfTransformation, [status(thm)], [f_79])).
% 30.21/20.68  tff(c_104, plain, (![A_87]: (~r1_tarski(A_87, '#skF_1'(A_87)) | v1_xboole_0(A_87))), inference(resolution, [status(thm)], [c_4, c_99])).
% 30.21/20.68  tff(c_109, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_104])).
% 30.21/20.68  tff(c_78, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_202])).
% 30.21/20.68  tff(c_329, plain, (![C_121, A_122, B_123]: (v4_relat_1(C_121, A_122) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 30.21/20.68  tff(c_342, plain, (v4_relat_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_78, c_329])).
% 30.21/20.68  tff(c_76, plain, (m1_subset_1('#skF_8', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_202])).
% 30.21/20.68  tff(c_962, plain, (![A_190, B_191, C_192]: (k1_relset_1(A_190, B_191, C_192)=k1_relat_1(C_192) | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(A_190, B_191))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 30.21/20.68  tff(c_978, plain, (k1_relset_1('#skF_5', '#skF_3', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_78, c_962])).
% 30.21/20.68  tff(c_823, plain, (![A_180, B_181, C_182]: (k2_relset_1(A_180, B_181, C_182)=k2_relat_1(C_182) | ~m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1(A_180, B_181))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 30.21/20.68  tff(c_835, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_82, c_823])).
% 30.21/20.68  tff(c_74, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_202])).
% 30.21/20.68  tff(c_917, plain, (r1_tarski(k2_relat_1('#skF_6'), k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_835, c_74])).
% 30.21/20.68  tff(c_983, plain, (r1_tarski(k2_relat_1('#skF_6'), k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_978, c_917])).
% 30.21/20.68  tff(c_80, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_202])).
% 30.21/20.68  tff(c_2581, plain, (![F_290, C_289, A_287, B_288, E_291, D_286]: (k1_funct_1(k8_funct_2(B_288, C_289, A_287, D_286, E_291), F_290)=k1_funct_1(E_291, k1_funct_1(D_286, F_290)) | k1_xboole_0=B_288 | ~r1_tarski(k2_relset_1(B_288, C_289, D_286), k1_relset_1(C_289, A_287, E_291)) | ~m1_subset_1(F_290, B_288) | ~m1_subset_1(E_291, k1_zfmisc_1(k2_zfmisc_1(C_289, A_287))) | ~v1_funct_1(E_291) | ~m1_subset_1(D_286, k1_zfmisc_1(k2_zfmisc_1(B_288, C_289))) | ~v1_funct_2(D_286, B_288, C_289) | ~v1_funct_1(D_286) | v1_xboole_0(C_289))), inference(cnfTransformation, [status(thm)], [f_177])).
% 30.21/20.68  tff(c_2589, plain, (![B_288, D_286, F_290]: (k1_funct_1(k8_funct_2(B_288, '#skF_5', '#skF_3', D_286, '#skF_7'), F_290)=k1_funct_1('#skF_7', k1_funct_1(D_286, F_290)) | k1_xboole_0=B_288 | ~r1_tarski(k2_relset_1(B_288, '#skF_5', D_286), k1_relat_1('#skF_7')) | ~m1_subset_1(F_290, B_288) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3'))) | ~v1_funct_1('#skF_7') | ~m1_subset_1(D_286, k1_zfmisc_1(k2_zfmisc_1(B_288, '#skF_5'))) | ~v1_funct_2(D_286, B_288, '#skF_5') | ~v1_funct_1(D_286) | v1_xboole_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_978, c_2581])).
% 30.21/20.68  tff(c_2604, plain, (![B_288, D_286, F_290]: (k1_funct_1(k8_funct_2(B_288, '#skF_5', '#skF_3', D_286, '#skF_7'), F_290)=k1_funct_1('#skF_7', k1_funct_1(D_286, F_290)) | k1_xboole_0=B_288 | ~r1_tarski(k2_relset_1(B_288, '#skF_5', D_286), k1_relat_1('#skF_7')) | ~m1_subset_1(F_290, B_288) | ~m1_subset_1(D_286, k1_zfmisc_1(k2_zfmisc_1(B_288, '#skF_5'))) | ~v1_funct_2(D_286, B_288, '#skF_5') | ~v1_funct_1(D_286) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_2589])).
% 30.21/20.68  tff(c_2988, plain, (![B_318, D_319, F_320]: (k1_funct_1(k8_funct_2(B_318, '#skF_5', '#skF_3', D_319, '#skF_7'), F_320)=k1_funct_1('#skF_7', k1_funct_1(D_319, F_320)) | k1_xboole_0=B_318 | ~r1_tarski(k2_relset_1(B_318, '#skF_5', D_319), k1_relat_1('#skF_7')) | ~m1_subset_1(F_320, B_318) | ~m1_subset_1(D_319, k1_zfmisc_1(k2_zfmisc_1(B_318, '#skF_5'))) | ~v1_funct_2(D_319, B_318, '#skF_5') | ~v1_funct_1(D_319))), inference(negUnitSimplification, [status(thm)], [c_88, c_2604])).
% 30.21/20.68  tff(c_2993, plain, (![F_320]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_320)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_320)) | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relat_1('#skF_6'), k1_relat_1('#skF_7')) | ~m1_subset_1(F_320, '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_835, c_2988])).
% 30.21/20.68  tff(c_3000, plain, (![F_320]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_320)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_320)) | k1_xboole_0='#skF_4' | ~m1_subset_1(F_320, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_983, c_2993])).
% 30.21/20.68  tff(c_3001, plain, (![F_320]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_320)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_320)) | ~m1_subset_1(F_320, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_72, c_3000])).
% 30.21/20.68  tff(c_18, plain, (![B_12]: (r1_tarski(B_12, B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 30.21/20.68  tff(c_977, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_82, c_962])).
% 30.21/20.68  tff(c_1993, plain, (![B_255, A_256, C_257]: (k1_xboole_0=B_255 | k1_relset_1(A_256, B_255, C_257)=A_256 | ~v1_funct_2(C_257, A_256, B_255) | ~m1_subset_1(C_257, k1_zfmisc_1(k2_zfmisc_1(A_256, B_255))))), inference(cnfTransformation, [status(thm)], [f_142])).
% 30.21/20.68  tff(c_2012, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_82, c_1993])).
% 30.21/20.68  tff(c_2019, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_977, c_2012])).
% 30.21/20.68  tff(c_2022, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_2019])).
% 30.21/20.68  tff(c_28, plain, (![B_19, A_18]: (v4_relat_1(B_19, A_18) | ~r1_tarski(k1_relat_1(B_19), A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_66])).
% 30.21/20.68  tff(c_2056, plain, (![A_18]: (v4_relat_1('#skF_6', A_18) | ~r1_tarski('#skF_4', A_18) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2022, c_28])).
% 30.21/20.68  tff(c_2087, plain, (![A_18]: (v4_relat_1('#skF_6', A_18) | ~r1_tarski('#skF_4', A_18))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_2056])).
% 30.21/20.68  tff(c_702, plain, (![C_167, A_168, B_169]: (v1_xboole_0(C_167) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_168, B_169))) | ~v1_xboole_0(A_168))), inference(cnfTransformation, [status(thm)], [f_96])).
% 30.21/20.68  tff(c_714, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_82, c_702])).
% 30.21/20.68  tff(c_716, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_714])).
% 30.21/20.68  tff(c_30, plain, (![B_19, A_18]: (r1_tarski(k1_relat_1(B_19), A_18) | ~v4_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_66])).
% 30.21/20.68  tff(c_22, plain, (![A_14, B_15]: (r2_hidden(A_14, B_15) | v1_xboole_0(B_15) | ~m1_subset_1(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 30.21/20.68  tff(c_552, plain, (![C_153, B_154, A_155]: (r2_hidden(C_153, B_154) | ~r2_hidden(C_153, A_155) | ~r1_tarski(A_155, B_154))), inference(cnfTransformation, [status(thm)], [f_38])).
% 30.21/20.68  tff(c_4155, plain, (![A_366, B_367, B_368]: (r2_hidden(A_366, B_367) | ~r1_tarski(B_368, B_367) | v1_xboole_0(B_368) | ~m1_subset_1(A_366, B_368))), inference(resolution, [status(thm)], [c_22, c_552])).
% 30.21/20.68  tff(c_22114, plain, (![A_832, A_833, B_834]: (r2_hidden(A_832, A_833) | v1_xboole_0(k1_relat_1(B_834)) | ~m1_subset_1(A_832, k1_relat_1(B_834)) | ~v4_relat_1(B_834, A_833) | ~v1_relat_1(B_834))), inference(resolution, [status(thm)], [c_30, c_4155])).
% 30.21/20.68  tff(c_22146, plain, (![A_832, A_833]: (r2_hidden(A_832, A_833) | v1_xboole_0(k1_relat_1('#skF_6')) | ~m1_subset_1(A_832, '#skF_4') | ~v4_relat_1('#skF_6', A_833) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2022, c_22114])).
% 30.21/20.68  tff(c_22170, plain, (![A_832, A_833]: (r2_hidden(A_832, A_833) | v1_xboole_0('#skF_4') | ~m1_subset_1(A_832, '#skF_4') | ~v4_relat_1('#skF_6', A_833))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_2022, c_22146])).
% 30.21/20.68  tff(c_22226, plain, (![A_835, A_836]: (r2_hidden(A_835, A_836) | ~m1_subset_1(A_835, '#skF_4') | ~v4_relat_1('#skF_6', A_836))), inference(negUnitSimplification, [status(thm)], [c_716, c_22170])).
% 30.21/20.68  tff(c_22277, plain, (![A_835, A_18]: (r2_hidden(A_835, A_18) | ~m1_subset_1(A_835, '#skF_4') | ~r1_tarski('#skF_4', A_18))), inference(resolution, [status(thm)], [c_2087, c_22226])).
% 30.21/20.68  tff(c_467, plain, (![C_138, B_139, A_140]: (v5_relat_1(C_138, B_139) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_140, B_139))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 30.21/20.68  tff(c_480, plain, (v5_relat_1('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_78, c_467])).
% 30.21/20.68  tff(c_142, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_78, c_129])).
% 30.21/20.68  tff(c_1312, plain, (![B_219, A_220]: (r2_hidden(k1_funct_1(B_219, A_220), k2_relat_1(B_219)) | ~r2_hidden(A_220, k1_relat_1(B_219)) | ~v1_funct_1(B_219) | ~v1_relat_1(B_219))), inference(cnfTransformation, [status(thm)], [f_74])).
% 30.21/20.68  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 30.21/20.68  tff(c_7794, plain, (![B_495, A_496, B_497]: (r2_hidden(k1_funct_1(B_495, A_496), B_497) | ~r1_tarski(k2_relat_1(B_495), B_497) | ~r2_hidden(A_496, k1_relat_1(B_495)) | ~v1_funct_1(B_495) | ~v1_relat_1(B_495))), inference(resolution, [status(thm)], [c_1312, c_6])).
% 30.21/20.68  tff(c_66, plain, (![A_47, B_48, C_50]: (k7_partfun1(A_47, B_48, C_50)=k1_funct_1(B_48, C_50) | ~r2_hidden(C_50, k1_relat_1(B_48)) | ~v1_funct_1(B_48) | ~v5_relat_1(B_48, A_47) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_153])).
% 30.21/20.68  tff(c_30619, plain, (![A_991, B_992, B_993, A_994]: (k7_partfun1(A_991, B_992, k1_funct_1(B_993, A_994))=k1_funct_1(B_992, k1_funct_1(B_993, A_994)) | ~v1_funct_1(B_992) | ~v5_relat_1(B_992, A_991) | ~v1_relat_1(B_992) | ~r1_tarski(k2_relat_1(B_993), k1_relat_1(B_992)) | ~r2_hidden(A_994, k1_relat_1(B_993)) | ~v1_funct_1(B_993) | ~v1_relat_1(B_993))), inference(resolution, [status(thm)], [c_7794, c_66])).
% 30.21/20.68  tff(c_30671, plain, (![A_991, A_994]: (k7_partfun1(A_991, '#skF_7', k1_funct_1('#skF_6', A_994))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', A_994)) | ~v1_funct_1('#skF_7') | ~v5_relat_1('#skF_7', A_991) | ~v1_relat_1('#skF_7') | ~r2_hidden(A_994, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_983, c_30619])).
% 30.21/20.68  tff(c_64058, plain, (![A_1378, A_1379]: (k7_partfun1(A_1378, '#skF_7', k1_funct_1('#skF_6', A_1379))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', A_1379)) | ~v5_relat_1('#skF_7', A_1378) | ~r2_hidden(A_1379, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_86, c_2022, c_142, c_80, c_30671])).
% 30.21/20.68  tff(c_70, plain, (k7_partfun1('#skF_3', '#skF_7', k1_funct_1('#skF_6', '#skF_8'))!=k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_202])).
% 30.21/20.68  tff(c_64064, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | ~v5_relat_1('#skF_7', '#skF_3') | ~r2_hidden('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_64058, c_70])).
% 30.21/20.68  tff(c_64070, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | ~r2_hidden('#skF_8', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_480, c_64064])).
% 30.21/20.68  tff(c_106832, plain, (~r2_hidden('#skF_8', '#skF_4')), inference(splitLeft, [status(thm)], [c_64070])).
% 30.21/20.68  tff(c_106835, plain, (~m1_subset_1('#skF_8', '#skF_4') | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_22277, c_106832])).
% 30.21/20.68  tff(c_106845, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_76, c_106835])).
% 30.21/20.68  tff(c_106846, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_64070])).
% 30.21/20.68  tff(c_109545, plain, (~m1_subset_1('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3001, c_106846])).
% 30.21/20.68  tff(c_109549, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_109545])).
% 30.21/20.68  tff(c_109550, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_2019])).
% 30.21/20.68  tff(c_582, plain, (![A_159, B_160]: (r2_hidden('#skF_1'(A_159), B_160) | ~r1_tarski(A_159, B_160) | v1_xboole_0(A_159))), inference(resolution, [status(thm)], [c_4, c_552])).
% 30.21/20.68  tff(c_34, plain, (![B_23, A_22]: (~r1_tarski(B_23, A_22) | ~r2_hidden(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_79])).
% 30.21/20.68  tff(c_629, plain, (![B_163, A_164]: (~r1_tarski(B_163, '#skF_1'(A_164)) | ~r1_tarski(A_164, B_163) | v1_xboole_0(A_164))), inference(resolution, [status(thm)], [c_582, c_34])).
% 30.21/20.68  tff(c_650, plain, (![A_165]: (~r1_tarski(A_165, k1_xboole_0) | v1_xboole_0(A_165))), inference(resolution, [status(thm)], [c_20, c_629])).
% 30.21/20.68  tff(c_667, plain, (![B_19]: (v1_xboole_0(k1_relat_1(B_19)) | ~v4_relat_1(B_19, k1_xboole_0) | ~v1_relat_1(B_19))), inference(resolution, [status(thm)], [c_30, c_650])).
% 30.21/20.68  tff(c_206, plain, (![A_105, B_106]: (r2_hidden('#skF_2'(A_105, B_106), A_105) | r1_tarski(A_105, B_106))), inference(cnfTransformation, [status(thm)], [f_38])).
% 30.21/20.68  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 30.21/20.68  tff(c_215, plain, (![A_107, B_108]: (~v1_xboole_0(A_107) | r1_tarski(A_107, B_108))), inference(resolution, [status(thm)], [c_206, c_2])).
% 30.21/20.68  tff(c_14, plain, (![B_12, A_11]: (B_12=A_11 | ~r1_tarski(B_12, A_11) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 30.21/20.68  tff(c_240, plain, (![B_110, A_111]: (B_110=A_111 | ~r1_tarski(B_110, A_111) | ~v1_xboole_0(A_111))), inference(resolution, [status(thm)], [c_215, c_14])).
% 30.21/20.68  tff(c_261, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relset_1('#skF_5', '#skF_3', '#skF_7') | ~v1_xboole_0(k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(resolution, [status(thm)], [c_74, c_240])).
% 30.21/20.68  tff(c_320, plain, (~v1_xboole_0(k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(splitLeft, [status(thm)], [c_261])).
% 30.21/20.68  tff(c_984, plain, (~v1_xboole_0(k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_978, c_320])).
% 30.21/20.68  tff(c_991, plain, (~v4_relat_1('#skF_7', k1_xboole_0) | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_667, c_984])).
% 30.21/20.68  tff(c_994, plain, (~v4_relat_1('#skF_7', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_142, c_991])).
% 30.21/20.68  tff(c_109569, plain, (~v4_relat_1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_109550, c_994])).
% 30.21/20.68  tff(c_109594, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_342, c_109569])).
% 30.21/20.68  tff(c_109596, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_714])).
% 30.21/20.68  tff(c_12, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 30.21/20.68  tff(c_109625, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_109596, c_12])).
% 30.21/20.68  tff(c_109632, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_109625])).
% 30.21/20.68  tff(c_109634, plain, (v1_xboole_0(k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(splitRight, [status(thm)], [c_261])).
% 30.21/20.68  tff(c_109652, plain, (k1_relset_1('#skF_5', '#skF_3', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_109634, c_12])).
% 30.21/20.68  tff(c_109655, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_109652, c_74])).
% 30.21/20.68  tff(c_231, plain, (![B_108, A_107]: (B_108=A_107 | ~r1_tarski(B_108, A_107) | ~v1_xboole_0(A_107))), inference(resolution, [status(thm)], [c_215, c_14])).
% 30.21/20.68  tff(c_109667, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_109655, c_231])).
% 30.21/20.68  tff(c_109676, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_109, c_109667])).
% 30.21/20.68  tff(c_110184, plain, (![A_1758, B_1759, C_1760]: (k2_relset_1(A_1758, B_1759, C_1760)=k2_relat_1(C_1760) | ~m1_subset_1(C_1760, k1_zfmisc_1(k2_zfmisc_1(A_1758, B_1759))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 30.21/20.68  tff(c_110194, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_82, c_110184])).
% 30.21/20.68  tff(c_110200, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_109676, c_110194])).
% 30.21/20.68  tff(c_110323, plain, (![B_1773, A_1774]: (r2_hidden(k1_funct_1(B_1773, A_1774), k2_relat_1(B_1773)) | ~r2_hidden(A_1774, k1_relat_1(B_1773)) | ~v1_funct_1(B_1773) | ~v1_relat_1(B_1773))), inference(cnfTransformation, [status(thm)], [f_74])).
% 30.21/20.68  tff(c_110334, plain, (![A_1774]: (r2_hidden(k1_funct_1('#skF_6', A_1774), k1_xboole_0) | ~r2_hidden(A_1774, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_110200, c_110323])).
% 30.21/20.68  tff(c_110480, plain, (![A_1790]: (r2_hidden(k1_funct_1('#skF_6', A_1790), k1_xboole_0) | ~r2_hidden(A_1790, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_86, c_110334])).
% 30.21/20.68  tff(c_110485, plain, (![A_1790]: (~r1_tarski(k1_xboole_0, k1_funct_1('#skF_6', A_1790)) | ~r2_hidden(A_1790, k1_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_110480, c_34])).
% 30.21/20.68  tff(c_110498, plain, (![A_1791]: (~r2_hidden(A_1791, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_110485])).
% 30.21/20.68  tff(c_110518, plain, (v1_xboole_0(k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_4, c_110498])).
% 30.21/20.68  tff(c_110544, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_110518, c_12])).
% 30.21/20.68  tff(c_110216, plain, (![A_1762, B_1763, C_1764]: (k1_relset_1(A_1762, B_1763, C_1764)=k1_relat_1(C_1764) | ~m1_subset_1(C_1764, k1_zfmisc_1(k2_zfmisc_1(A_1762, B_1763))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 30.21/20.68  tff(c_110231, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_82, c_110216])).
% 30.21/20.68  tff(c_110557, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_110544, c_110231])).
% 30.21/20.68  tff(c_110624, plain, (![B_1796, A_1797, C_1798]: (k1_xboole_0=B_1796 | k1_relset_1(A_1797, B_1796, C_1798)=A_1797 | ~v1_funct_2(C_1798, A_1797, B_1796) | ~m1_subset_1(C_1798, k1_zfmisc_1(k2_zfmisc_1(A_1797, B_1796))))), inference(cnfTransformation, [status(thm)], [f_142])).
% 30.21/20.68  tff(c_110637, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_82, c_110624])).
% 30.21/20.68  tff(c_110644, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_110557, c_110637])).
% 30.21/20.68  tff(c_110645, plain, (k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_72, c_110644])).
% 30.21/20.68  tff(c_110681, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_110645, c_109])).
% 30.21/20.68  tff(c_110686, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_110681])).
% 30.21/20.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 30.21/20.68  
% 30.21/20.68  Inference rules
% 30.21/20.68  ----------------------
% 30.21/20.68  #Ref     : 0
% 30.21/20.68  #Sup     : 26411
% 30.21/20.68  #Fact    : 0
% 30.21/20.68  #Define  : 0
% 30.21/20.68  #Split   : 71
% 30.21/20.68  #Chain   : 0
% 30.21/20.68  #Close   : 0
% 30.21/20.68  
% 30.21/20.68  Ordering : KBO
% 30.21/20.68  
% 30.21/20.68  Simplification rules
% 30.21/20.68  ----------------------
% 30.21/20.68  #Subsume      : 11364
% 30.21/20.68  #Demod        : 26216
% 30.21/20.68  #Tautology    : 7551
% 30.21/20.68  #SimpNegUnit  : 289
% 30.21/20.68  #BackRed      : 198
% 30.21/20.68  
% 30.21/20.68  #Partial instantiations: 0
% 30.21/20.68  #Strategies tried      : 1
% 30.21/20.68  
% 30.21/20.68  Timing (in seconds)
% 30.21/20.68  ----------------------
% 30.21/20.69  Preprocessing        : 0.37
% 30.21/20.69  Parsing              : 0.20
% 30.21/20.69  CNF conversion       : 0.03
% 30.21/20.69  Main loop            : 19.52
% 30.21/20.69  Inferencing          : 2.57
% 30.21/20.69  Reduction            : 5.89
% 30.21/20.69  Demodulation         : 4.21
% 30.21/20.69  BG Simplification    : 0.31
% 30.21/20.69  Subsumption          : 10.07
% 30.21/20.69  Abstraction          : 0.60
% 30.21/20.69  MUC search           : 0.00
% 30.21/20.69  Cooper               : 0.00
% 30.21/20.69  Total                : 19.95
% 30.21/20.69  Index Insertion      : 0.00
% 30.21/20.69  Index Deletion       : 0.00
% 30.21/20.69  Index Matching       : 0.00
% 30.21/20.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
