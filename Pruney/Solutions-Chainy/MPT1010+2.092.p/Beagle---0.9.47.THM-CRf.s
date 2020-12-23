%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:17 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 106 expanded)
%              Number of leaves         :   43 (  57 expanded)
%              Depth                    :   10
%              Number of atoms          :  108 ( 194 expanded)
%              Number of equality atoms :   27 (  56 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_130,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_76,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_119,axiom,(
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

tff(f_86,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,A)
        & v1_funct_1(C) )
     => ( r2_hidden(B,k1_relat_1(C))
       => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_91,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_78,plain,(
    k1_funct_1('#skF_9','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_82,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6',k1_tarski('#skF_7')))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_286,plain,(
    ! [C_98,B_99,A_100] :
      ( v5_relat_1(C_98,B_99)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_100,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_290,plain,(
    v5_relat_1('#skF_9',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_82,c_286])).

tff(c_80,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_54,plain,(
    ! [A_29,B_30] : v1_relat_1(k2_zfmisc_1(A_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_244,plain,(
    ! [B_89,A_90] :
      ( v1_relat_1(B_89)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_90))
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_247,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6',k1_tarski('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_82,c_244])).

tff(c_250,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_247])).

tff(c_86,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_84,plain,(
    v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_542,plain,(
    ! [A_134,B_135,C_136] :
      ( k1_relset_1(A_134,B_135,C_136) = k1_relat_1(C_136)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_546,plain,(
    k1_relset_1('#skF_6',k1_tarski('#skF_7'),'#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_82,c_542])).

tff(c_718,plain,(
    ! [B_168,A_169,C_170] :
      ( k1_xboole_0 = B_168
      | k1_relset_1(A_169,B_168,C_170) = A_169
      | ~ v1_funct_2(C_170,A_169,B_168)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(A_169,B_168))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_721,plain,
    ( k1_tarski('#skF_7') = k1_xboole_0
    | k1_relset_1('#skF_6',k1_tarski('#skF_7'),'#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_82,c_718])).

tff(c_724,plain,
    ( k1_tarski('#skF_7') = k1_xboole_0
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_546,c_721])).

tff(c_725,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_724])).

tff(c_56,plain,(
    ! [C_33,B_32,A_31] :
      ( m1_subset_1(k1_funct_1(C_33,B_32),A_31)
      | ~ r2_hidden(B_32,k1_relat_1(C_33))
      | ~ v1_funct_1(C_33)
      | ~ v5_relat_1(C_33,A_31)
      | ~ v1_relat_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_735,plain,(
    ! [B_32,A_31] :
      ( m1_subset_1(k1_funct_1('#skF_9',B_32),A_31)
      | ~ r2_hidden(B_32,'#skF_6')
      | ~ v1_funct_1('#skF_9')
      | ~ v5_relat_1('#skF_9',A_31)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_725,c_56])).

tff(c_745,plain,(
    ! [B_174,A_175] :
      ( m1_subset_1(k1_funct_1('#skF_9',B_174),A_175)
      | ~ r2_hidden(B_174,'#skF_6')
      | ~ v5_relat_1('#skF_9',A_175) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_86,c_735])).

tff(c_34,plain,(
    ! [C_17] : r2_hidden(C_17,k1_tarski(C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_99,plain,(
    ! [B_50,A_51] :
      ( ~ r2_hidden(B_50,A_51)
      | ~ v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_106,plain,(
    ! [C_17] : ~ v1_xboole_0(k1_tarski(C_17)) ),
    inference(resolution,[status(thm)],[c_34,c_99])).

tff(c_260,plain,(
    ! [A_95,B_96] :
      ( r2_hidden(A_95,B_96)
      | v1_xboole_0(B_96)
      | ~ m1_subset_1(A_95,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_32,plain,(
    ! [C_17,A_13] :
      ( C_17 = A_13
      | ~ r2_hidden(C_17,k1_tarski(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_267,plain,(
    ! [A_95,A_13] :
      ( A_95 = A_13
      | v1_xboole_0(k1_tarski(A_13))
      | ~ m1_subset_1(A_95,k1_tarski(A_13)) ) ),
    inference(resolution,[status(thm)],[c_260,c_32])).

tff(c_274,plain,(
    ! [A_95,A_13] :
      ( A_95 = A_13
      | ~ m1_subset_1(A_95,k1_tarski(A_13)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_267])).

tff(c_806,plain,(
    ! [B_176,A_177] :
      ( k1_funct_1('#skF_9',B_176) = A_177
      | ~ r2_hidden(B_176,'#skF_6')
      | ~ v5_relat_1('#skF_9',k1_tarski(A_177)) ) ),
    inference(resolution,[status(thm)],[c_745,c_274])).

tff(c_830,plain,(
    ! [A_178] :
      ( k1_funct_1('#skF_9','#skF_8') = A_178
      | ~ v5_relat_1('#skF_9',k1_tarski(A_178)) ) ),
    inference(resolution,[status(thm)],[c_80,c_806])).

tff(c_833,plain,(
    k1_funct_1('#skF_9','#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_290,c_830])).

tff(c_837,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_833])).

tff(c_838,plain,(
    k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_724])).

tff(c_157,plain,(
    ! [B_69,A_70] :
      ( ~ r1_tarski(B_69,A_70)
      | ~ r2_hidden(A_70,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_180,plain,(
    ! [C_17] : ~ r1_tarski(k1_tarski(C_17),C_17) ),
    inference(resolution,[status(thm)],[c_34,c_157])).

tff(c_865,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_838,c_180])).

tff(c_886,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_865])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:16:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.11/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.48  
% 3.22/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.48  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 3.22/1.48  
% 3.22/1.48  %Foreground sorts:
% 3.22/1.48  
% 3.22/1.48  
% 3.22/1.48  %Background operators:
% 3.22/1.48  
% 3.22/1.48  
% 3.22/1.48  %Foreground operators:
% 3.22/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.22/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.22/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.22/1.48  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.22/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.22/1.48  tff('#skF_7', type, '#skF_7': $i).
% 3.22/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.22/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.22/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.22/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.22/1.48  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.22/1.48  tff('#skF_6', type, '#skF_6': $i).
% 3.22/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.22/1.48  tff('#skF_9', type, '#skF_9': $i).
% 3.22/1.48  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.22/1.48  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.22/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.22/1.48  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.22/1.48  tff('#skF_8', type, '#skF_8': $i).
% 3.22/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.22/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.22/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.48  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.22/1.48  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.22/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.22/1.48  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.22/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.22/1.48  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.22/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.22/1.48  
% 3.22/1.50  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.22/1.50  tff(f_130, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 3.22/1.50  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.22/1.50  tff(f_76, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.22/1.50  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.22/1.50  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.22/1.50  tff(f_119, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.22/1.50  tff(f_86, axiom, (![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_1)).
% 3.22/1.50  tff(f_55, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.22/1.50  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.22/1.50  tff(f_67, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.22/1.50  tff(f_91, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.22/1.50  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.22/1.50  tff(c_78, plain, (k1_funct_1('#skF_9', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.22/1.50  tff(c_82, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', k1_tarski('#skF_7'))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.22/1.50  tff(c_286, plain, (![C_98, B_99, A_100]: (v5_relat_1(C_98, B_99) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_100, B_99))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.22/1.50  tff(c_290, plain, (v5_relat_1('#skF_9', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_82, c_286])).
% 3.22/1.50  tff(c_80, plain, (r2_hidden('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.22/1.50  tff(c_54, plain, (![A_29, B_30]: (v1_relat_1(k2_zfmisc_1(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.22/1.50  tff(c_244, plain, (![B_89, A_90]: (v1_relat_1(B_89) | ~m1_subset_1(B_89, k1_zfmisc_1(A_90)) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.22/1.50  tff(c_247, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_6', k1_tarski('#skF_7')))), inference(resolution, [status(thm)], [c_82, c_244])).
% 3.22/1.50  tff(c_250, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_247])).
% 3.22/1.50  tff(c_86, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.22/1.50  tff(c_84, plain, (v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.22/1.50  tff(c_542, plain, (![A_134, B_135, C_136]: (k1_relset_1(A_134, B_135, C_136)=k1_relat_1(C_136) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.22/1.50  tff(c_546, plain, (k1_relset_1('#skF_6', k1_tarski('#skF_7'), '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_82, c_542])).
% 3.22/1.50  tff(c_718, plain, (![B_168, A_169, C_170]: (k1_xboole_0=B_168 | k1_relset_1(A_169, B_168, C_170)=A_169 | ~v1_funct_2(C_170, A_169, B_168) | ~m1_subset_1(C_170, k1_zfmisc_1(k2_zfmisc_1(A_169, B_168))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.22/1.50  tff(c_721, plain, (k1_tarski('#skF_7')=k1_xboole_0 | k1_relset_1('#skF_6', k1_tarski('#skF_7'), '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_82, c_718])).
% 3.22/1.50  tff(c_724, plain, (k1_tarski('#skF_7')=k1_xboole_0 | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_546, c_721])).
% 3.22/1.50  tff(c_725, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_724])).
% 3.22/1.50  tff(c_56, plain, (![C_33, B_32, A_31]: (m1_subset_1(k1_funct_1(C_33, B_32), A_31) | ~r2_hidden(B_32, k1_relat_1(C_33)) | ~v1_funct_1(C_33) | ~v5_relat_1(C_33, A_31) | ~v1_relat_1(C_33))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.22/1.50  tff(c_735, plain, (![B_32, A_31]: (m1_subset_1(k1_funct_1('#skF_9', B_32), A_31) | ~r2_hidden(B_32, '#skF_6') | ~v1_funct_1('#skF_9') | ~v5_relat_1('#skF_9', A_31) | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_725, c_56])).
% 3.22/1.50  tff(c_745, plain, (![B_174, A_175]: (m1_subset_1(k1_funct_1('#skF_9', B_174), A_175) | ~r2_hidden(B_174, '#skF_6') | ~v5_relat_1('#skF_9', A_175))), inference(demodulation, [status(thm), theory('equality')], [c_250, c_86, c_735])).
% 3.22/1.50  tff(c_34, plain, (![C_17]: (r2_hidden(C_17, k1_tarski(C_17)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.22/1.50  tff(c_99, plain, (![B_50, A_51]: (~r2_hidden(B_50, A_51) | ~v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.22/1.50  tff(c_106, plain, (![C_17]: (~v1_xboole_0(k1_tarski(C_17)))), inference(resolution, [status(thm)], [c_34, c_99])).
% 3.22/1.50  tff(c_260, plain, (![A_95, B_96]: (r2_hidden(A_95, B_96) | v1_xboole_0(B_96) | ~m1_subset_1(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.22/1.50  tff(c_32, plain, (![C_17, A_13]: (C_17=A_13 | ~r2_hidden(C_17, k1_tarski(A_13)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.22/1.50  tff(c_267, plain, (![A_95, A_13]: (A_95=A_13 | v1_xboole_0(k1_tarski(A_13)) | ~m1_subset_1(A_95, k1_tarski(A_13)))), inference(resolution, [status(thm)], [c_260, c_32])).
% 3.22/1.50  tff(c_274, plain, (![A_95, A_13]: (A_95=A_13 | ~m1_subset_1(A_95, k1_tarski(A_13)))), inference(negUnitSimplification, [status(thm)], [c_106, c_267])).
% 3.22/1.50  tff(c_806, plain, (![B_176, A_177]: (k1_funct_1('#skF_9', B_176)=A_177 | ~r2_hidden(B_176, '#skF_6') | ~v5_relat_1('#skF_9', k1_tarski(A_177)))), inference(resolution, [status(thm)], [c_745, c_274])).
% 3.22/1.50  tff(c_830, plain, (![A_178]: (k1_funct_1('#skF_9', '#skF_8')=A_178 | ~v5_relat_1('#skF_9', k1_tarski(A_178)))), inference(resolution, [status(thm)], [c_80, c_806])).
% 3.22/1.50  tff(c_833, plain, (k1_funct_1('#skF_9', '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_290, c_830])).
% 3.22/1.50  tff(c_837, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_833])).
% 3.22/1.50  tff(c_838, plain, (k1_tarski('#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_724])).
% 3.22/1.50  tff(c_157, plain, (![B_69, A_70]: (~r1_tarski(B_69, A_70) | ~r2_hidden(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.22/1.50  tff(c_180, plain, (![C_17]: (~r1_tarski(k1_tarski(C_17), C_17))), inference(resolution, [status(thm)], [c_34, c_157])).
% 3.22/1.50  tff(c_865, plain, (~r1_tarski(k1_xboole_0, '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_838, c_180])).
% 3.22/1.50  tff(c_886, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_865])).
% 3.22/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.50  
% 3.22/1.50  Inference rules
% 3.22/1.50  ----------------------
% 3.22/1.50  #Ref     : 0
% 3.22/1.50  #Sup     : 167
% 3.22/1.50  #Fact    : 2
% 3.22/1.50  #Define  : 0
% 3.22/1.50  #Split   : 1
% 3.22/1.50  #Chain   : 0
% 3.22/1.50  #Close   : 0
% 3.22/1.50  
% 3.22/1.50  Ordering : KBO
% 3.22/1.50  
% 3.22/1.50  Simplification rules
% 3.22/1.50  ----------------------
% 3.22/1.50  #Subsume      : 27
% 3.22/1.50  #Demod        : 75
% 3.22/1.50  #Tautology    : 67
% 3.22/1.50  #SimpNegUnit  : 17
% 3.22/1.50  #BackRed      : 5
% 3.22/1.50  
% 3.22/1.50  #Partial instantiations: 0
% 3.22/1.50  #Strategies tried      : 1
% 3.22/1.50  
% 3.22/1.50  Timing (in seconds)
% 3.22/1.50  ----------------------
% 3.22/1.50  Preprocessing        : 0.35
% 3.22/1.50  Parsing              : 0.18
% 3.22/1.50  CNF conversion       : 0.03
% 3.22/1.50  Main loop            : 0.39
% 3.22/1.50  Inferencing          : 0.14
% 3.22/1.50  Reduction            : 0.12
% 3.22/1.50  Demodulation         : 0.08
% 3.22/1.50  BG Simplification    : 0.02
% 3.22/1.50  Subsumption          : 0.07
% 3.22/1.50  Abstraction          : 0.02
% 3.22/1.50  MUC search           : 0.00
% 3.22/1.50  Cooper               : 0.00
% 3.22/1.50  Total                : 0.77
% 3.22/1.50  Index Insertion      : 0.00
% 3.22/1.50  Index Deletion       : 0.00
% 3.22/1.50  Index Matching       : 0.00
% 3.22/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
