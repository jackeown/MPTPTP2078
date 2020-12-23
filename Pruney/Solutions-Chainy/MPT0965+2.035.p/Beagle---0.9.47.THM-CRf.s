%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:04 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   77 (  99 expanded)
%              Number of leaves         :   38 (  52 expanded)
%              Depth                    :    8
%              Number of atoms          :  114 ( 198 expanded)
%              Number of equality atoms :   22 (  33 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_110,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_59,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_97,axiom,(
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

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,A)
        & v1_funct_1(C) )
     => ( r2_hidden(B,k1_relat_1(C))
       => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_152,plain,(
    ! [C_62,B_63,A_64] :
      ( v5_relat_1(C_62,B_63)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_64,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_156,plain,(
    v5_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_152])).

tff(c_87,plain,(
    ! [A_46,B_47] :
      ( r2_hidden('#skF_2'(A_46,B_47),A_46)
      | r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_95,plain,(
    ! [A_46] : r1_tarski(A_46,A_46) ),
    inference(resolution,[status(thm)],[c_87,c_8])).

tff(c_20,plain,(
    ! [A_19,B_20] : v1_relat_1(k2_zfmisc_1(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_66,plain,(
    ! [B_42,A_43] :
      ( v1_relat_1(B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_43))
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_69,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_48,c_66])).

tff(c_72,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_69])).

tff(c_52,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_50,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_210,plain,(
    ! [A_83,B_84,C_85] :
      ( k1_relset_1(A_83,B_84,C_85) = k1_relat_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_214,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_210])).

tff(c_273,plain,(
    ! [B_107,A_108,C_109] :
      ( k1_xboole_0 = B_107
      | k1_relset_1(A_108,B_107,C_109) = A_108
      | ~ v1_funct_2(C_109,A_108,B_107)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_108,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_276,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_273])).

tff(c_279,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_214,c_276])).

tff(c_280,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_279])).

tff(c_46,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_115,plain,(
    ! [C_54,B_55,A_56] :
      ( r2_hidden(C_54,B_55)
      | ~ r2_hidden(C_54,A_56)
      | ~ r1_tarski(A_56,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_127,plain,(
    ! [B_55] :
      ( r2_hidden('#skF_5',B_55)
      | ~ r1_tarski('#skF_3',B_55) ) ),
    inference(resolution,[status(thm)],[c_46,c_115])).

tff(c_236,plain,(
    ! [C_99,B_100,A_101] :
      ( m1_subset_1(k1_funct_1(C_99,B_100),A_101)
      | ~ r2_hidden(B_100,k1_relat_1(C_99))
      | ~ v1_funct_1(C_99)
      | ~ v5_relat_1(C_99,A_101)
      | ~ v1_relat_1(C_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_257,plain,(
    ! [C_99,A_101] :
      ( m1_subset_1(k1_funct_1(C_99,'#skF_5'),A_101)
      | ~ v1_funct_1(C_99)
      | ~ v5_relat_1(C_99,A_101)
      | ~ v1_relat_1(C_99)
      | ~ r1_tarski('#skF_3',k1_relat_1(C_99)) ) ),
    inference(resolution,[status(thm)],[c_127,c_236])).

tff(c_284,plain,(
    ! [A_101] :
      ( m1_subset_1(k1_funct_1('#skF_6','#skF_5'),A_101)
      | ~ v1_funct_1('#skF_6')
      | ~ v5_relat_1('#skF_6',A_101)
      | ~ v1_relat_1('#skF_6')
      | ~ r1_tarski('#skF_3','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_257])).

tff(c_298,plain,(
    ! [A_110] :
      ( m1_subset_1(k1_funct_1('#skF_6','#skF_5'),A_110)
      | ~ v5_relat_1('#skF_6',A_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_72,c_52,c_284])).

tff(c_73,plain,(
    ! [A_44,B_45] :
      ( r2_hidden(A_44,B_45)
      | v1_xboole_0(B_45)
      | ~ m1_subset_1(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_42,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_86,plain,
    ( v1_xboole_0('#skF_4')
    | ~ m1_subset_1(k1_funct_1('#skF_6','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_73,c_42])).

tff(c_105,plain,(
    ~ m1_subset_1(k1_funct_1('#skF_6','#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_333,plain,(
    ~ v5_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_298,c_105])).

tff(c_349,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_333])).

tff(c_350,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_98,plain,(
    ! [A_49,B_50] :
      ( ~ v1_xboole_0(A_49)
      | r1_tarski(A_49,B_50) ) ),
    inference(resolution,[status(thm)],[c_87,c_2])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k4_xboole_0(B_13,A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_103,plain,(
    ! [A_49] :
      ( k1_xboole_0 = A_49
      | ~ v1_xboole_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_98,c_14])).

tff(c_354,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_350,c_103])).

tff(c_358,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_354])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:27:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.30  
% 2.23/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.31  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 2.23/1.31  
% 2.23/1.31  %Foreground sorts:
% 2.23/1.31  
% 2.23/1.31  
% 2.23/1.31  %Background operators:
% 2.23/1.31  
% 2.23/1.31  
% 2.23/1.31  %Foreground operators:
% 2.23/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.23/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.23/1.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.23/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.23/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.23/1.31  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.23/1.31  tff('#skF_6', type, '#skF_6': $i).
% 2.23/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.31  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.23/1.31  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.23/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.23/1.31  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.23/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.23/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.23/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.23/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.23/1.31  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.23/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.23/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.23/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.23/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.23/1.31  
% 2.59/1.32  tff(f_110, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 2.59/1.32  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.59/1.32  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.59/1.32  tff(f_59, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.59/1.32  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.59/1.32  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.59/1.32  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.59/1.32  tff(f_69, axiom, (![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_1)).
% 2.59/1.32  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.59/1.32  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.59/1.32  tff(f_44, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 2.59/1.32  tff(c_44, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.59/1.32  tff(c_48, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.59/1.32  tff(c_152, plain, (![C_62, B_63, A_64]: (v5_relat_1(C_62, B_63) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_64, B_63))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.59/1.32  tff(c_156, plain, (v5_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_48, c_152])).
% 2.59/1.32  tff(c_87, plain, (![A_46, B_47]: (r2_hidden('#skF_2'(A_46, B_47), A_46) | r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.59/1.32  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.59/1.32  tff(c_95, plain, (![A_46]: (r1_tarski(A_46, A_46))), inference(resolution, [status(thm)], [c_87, c_8])).
% 2.59/1.32  tff(c_20, plain, (![A_19, B_20]: (v1_relat_1(k2_zfmisc_1(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.59/1.32  tff(c_66, plain, (![B_42, A_43]: (v1_relat_1(B_42) | ~m1_subset_1(B_42, k1_zfmisc_1(A_43)) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.59/1.32  tff(c_69, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_48, c_66])).
% 2.59/1.32  tff(c_72, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_69])).
% 2.59/1.32  tff(c_52, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.59/1.32  tff(c_50, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.59/1.32  tff(c_210, plain, (![A_83, B_84, C_85]: (k1_relset_1(A_83, B_84, C_85)=k1_relat_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.59/1.32  tff(c_214, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_48, c_210])).
% 2.59/1.32  tff(c_273, plain, (![B_107, A_108, C_109]: (k1_xboole_0=B_107 | k1_relset_1(A_108, B_107, C_109)=A_108 | ~v1_funct_2(C_109, A_108, B_107) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_108, B_107))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.59/1.32  tff(c_276, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_48, c_273])).
% 2.59/1.32  tff(c_279, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_214, c_276])).
% 2.59/1.32  tff(c_280, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_44, c_279])).
% 2.59/1.32  tff(c_46, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.59/1.32  tff(c_115, plain, (![C_54, B_55, A_56]: (r2_hidden(C_54, B_55) | ~r2_hidden(C_54, A_56) | ~r1_tarski(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.59/1.32  tff(c_127, plain, (![B_55]: (r2_hidden('#skF_5', B_55) | ~r1_tarski('#skF_3', B_55))), inference(resolution, [status(thm)], [c_46, c_115])).
% 2.59/1.32  tff(c_236, plain, (![C_99, B_100, A_101]: (m1_subset_1(k1_funct_1(C_99, B_100), A_101) | ~r2_hidden(B_100, k1_relat_1(C_99)) | ~v1_funct_1(C_99) | ~v5_relat_1(C_99, A_101) | ~v1_relat_1(C_99))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.59/1.32  tff(c_257, plain, (![C_99, A_101]: (m1_subset_1(k1_funct_1(C_99, '#skF_5'), A_101) | ~v1_funct_1(C_99) | ~v5_relat_1(C_99, A_101) | ~v1_relat_1(C_99) | ~r1_tarski('#skF_3', k1_relat_1(C_99)))), inference(resolution, [status(thm)], [c_127, c_236])).
% 2.59/1.32  tff(c_284, plain, (![A_101]: (m1_subset_1(k1_funct_1('#skF_6', '#skF_5'), A_101) | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', A_101) | ~v1_relat_1('#skF_6') | ~r1_tarski('#skF_3', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_280, c_257])).
% 2.59/1.32  tff(c_298, plain, (![A_110]: (m1_subset_1(k1_funct_1('#skF_6', '#skF_5'), A_110) | ~v5_relat_1('#skF_6', A_110))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_72, c_52, c_284])).
% 2.59/1.32  tff(c_73, plain, (![A_44, B_45]: (r2_hidden(A_44, B_45) | v1_xboole_0(B_45) | ~m1_subset_1(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.59/1.32  tff(c_42, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.59/1.32  tff(c_86, plain, (v1_xboole_0('#skF_4') | ~m1_subset_1(k1_funct_1('#skF_6', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_73, c_42])).
% 2.59/1.32  tff(c_105, plain, (~m1_subset_1(k1_funct_1('#skF_6', '#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_86])).
% 2.59/1.32  tff(c_333, plain, (~v5_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_298, c_105])).
% 2.59/1.32  tff(c_349, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_156, c_333])).
% 2.59/1.32  tff(c_350, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_86])).
% 2.59/1.32  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.59/1.32  tff(c_98, plain, (![A_49, B_50]: (~v1_xboole_0(A_49) | r1_tarski(A_49, B_50))), inference(resolution, [status(thm)], [c_87, c_2])).
% 2.59/1.32  tff(c_14, plain, (![A_12, B_13]: (k1_xboole_0=A_12 | ~r1_tarski(A_12, k4_xboole_0(B_13, A_12)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.59/1.32  tff(c_103, plain, (![A_49]: (k1_xboole_0=A_49 | ~v1_xboole_0(A_49))), inference(resolution, [status(thm)], [c_98, c_14])).
% 2.59/1.32  tff(c_354, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_350, c_103])).
% 2.59/1.32  tff(c_358, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_354])).
% 2.59/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.32  
% 2.59/1.32  Inference rules
% 2.59/1.32  ----------------------
% 2.59/1.32  #Ref     : 0
% 2.59/1.32  #Sup     : 67
% 2.59/1.32  #Fact    : 0
% 2.59/1.32  #Define  : 0
% 2.59/1.32  #Split   : 1
% 2.59/1.32  #Chain   : 0
% 2.59/1.32  #Close   : 0
% 2.59/1.32  
% 2.59/1.32  Ordering : KBO
% 2.59/1.32  
% 2.59/1.32  Simplification rules
% 2.59/1.32  ----------------------
% 2.59/1.32  #Subsume      : 12
% 2.59/1.32  #Demod        : 12
% 2.59/1.32  #Tautology    : 15
% 2.59/1.32  #SimpNegUnit  : 3
% 2.59/1.32  #BackRed      : 1
% 2.59/1.32  
% 2.59/1.32  #Partial instantiations: 0
% 2.59/1.32  #Strategies tried      : 1
% 2.59/1.32  
% 2.59/1.32  Timing (in seconds)
% 2.59/1.32  ----------------------
% 2.59/1.32  Preprocessing        : 0.30
% 2.59/1.32  Parsing              : 0.16
% 2.59/1.32  CNF conversion       : 0.02
% 2.59/1.33  Main loop            : 0.23
% 2.59/1.33  Inferencing          : 0.09
% 2.59/1.33  Reduction            : 0.06
% 2.59/1.33  Demodulation         : 0.04
% 2.59/1.33  BG Simplification    : 0.02
% 2.59/1.33  Subsumption          : 0.04
% 2.59/1.33  Abstraction          : 0.01
% 2.59/1.33  MUC search           : 0.00
% 2.59/1.33  Cooper               : 0.00
% 2.59/1.33  Total                : 0.57
% 2.59/1.33  Index Insertion      : 0.00
% 2.59/1.33  Index Deletion       : 0.00
% 2.59/1.33  Index Matching       : 0.00
% 2.59/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
