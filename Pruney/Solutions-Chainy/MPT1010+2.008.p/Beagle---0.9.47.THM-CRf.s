%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:06 EST 2020

% Result     : Theorem 7.50s
% Output     : CNFRefutation 7.50s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 122 expanded)
%              Number of leaves         :   46 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :  138 ( 236 expanded)
%              Number of equality atoms :   46 (  79 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_128,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_117,axiom,(
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

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_44,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_46,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_85,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_84,plain,(
    k1_funct_1('#skF_10','#skF_9') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_88,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_247,plain,(
    ! [C_131,B_132,A_133] :
      ( v5_relat_1(C_131,B_132)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_133,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_256,plain,(
    v5_relat_1('#skF_10',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_88,c_247])).

tff(c_195,plain,(
    ! [C_115,A_116,B_117] :
      ( v1_relat_1(C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_204,plain,(
    v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_88,c_195])).

tff(c_42,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k2_relat_1(B_22),A_21)
      | ~ v5_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_86,plain,(
    r2_hidden('#skF_9','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_92,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_90,plain,(
    v1_funct_2('#skF_10','#skF_7',k1_tarski('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_425,plain,(
    ! [A_183,B_184,C_185] :
      ( k1_relset_1(A_183,B_184,C_185) = k1_relat_1(C_185)
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(A_183,B_184))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_434,plain,(
    k1_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_88,c_425])).

tff(c_828,plain,(
    ! [B_262,A_263,C_264] :
      ( k1_xboole_0 = B_262
      | k1_relset_1(A_263,B_262,C_264) = A_263
      | ~ v1_funct_2(C_264,A_263,B_262)
      | ~ m1_subset_1(C_264,k1_zfmisc_1(k2_zfmisc_1(A_263,B_262))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_835,plain,
    ( k1_tarski('#skF_8') = k1_xboole_0
    | k1_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = '#skF_7'
    | ~ v1_funct_2('#skF_10','#skF_7',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_88,c_828])).

tff(c_839,plain,
    ( k1_tarski('#skF_8') = k1_xboole_0
    | k1_relat_1('#skF_10') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_434,c_835])).

tff(c_840,plain,(
    k1_relat_1('#skF_10') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_839])).

tff(c_38,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,k1_zfmisc_1(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_576,plain,(
    ! [A_228,D_229] :
      ( r2_hidden(k1_funct_1(A_228,D_229),k2_relat_1(A_228))
      | ~ r2_hidden(D_229,k1_relat_1(A_228))
      | ~ v1_funct_1(A_228)
      | ~ v1_relat_1(A_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_34,plain,(
    ! [C_18,A_15,B_16] :
      ( r2_hidden(C_18,A_15)
      | ~ r2_hidden(C_18,B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3110,plain,(
    ! [A_458,D_459,A_460] :
      ( r2_hidden(k1_funct_1(A_458,D_459),A_460)
      | ~ m1_subset_1(k2_relat_1(A_458),k1_zfmisc_1(A_460))
      | ~ r2_hidden(D_459,k1_relat_1(A_458))
      | ~ v1_funct_1(A_458)
      | ~ v1_relat_1(A_458) ) ),
    inference(resolution,[status(thm)],[c_576,c_34])).

tff(c_4690,plain,(
    ! [A_546,D_547,B_548] :
      ( r2_hidden(k1_funct_1(A_546,D_547),B_548)
      | ~ r2_hidden(D_547,k1_relat_1(A_546))
      | ~ v1_funct_1(A_546)
      | ~ v1_relat_1(A_546)
      | ~ r1_tarski(k2_relat_1(A_546),B_548) ) ),
    inference(resolution,[status(thm)],[c_38,c_3110])).

tff(c_28,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_30,plain,(
    ! [A_10,B_11] : k1_enumset1(A_10,A_10,B_11) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_312,plain,(
    ! [E_145,C_146,B_147,A_148] :
      ( E_145 = C_146
      | E_145 = B_147
      | E_145 = A_148
      | ~ r2_hidden(E_145,k1_enumset1(A_148,B_147,C_146)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_506,plain,(
    ! [E_215,B_216,A_217] :
      ( E_215 = B_216
      | E_215 = A_217
      | E_215 = A_217
      | ~ r2_hidden(E_215,k2_tarski(A_217,B_216)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_312])).

tff(c_519,plain,(
    ! [E_215,A_9] :
      ( E_215 = A_9
      | E_215 = A_9
      | E_215 = A_9
      | ~ r2_hidden(E_215,k1_tarski(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_506])).

tff(c_5459,plain,(
    ! [A_598,D_599,A_600] :
      ( k1_funct_1(A_598,D_599) = A_600
      | ~ r2_hidden(D_599,k1_relat_1(A_598))
      | ~ v1_funct_1(A_598)
      | ~ v1_relat_1(A_598)
      | ~ r1_tarski(k2_relat_1(A_598),k1_tarski(A_600)) ) ),
    inference(resolution,[status(thm)],[c_4690,c_519])).

tff(c_5542,plain,(
    ! [D_599,A_600] :
      ( k1_funct_1('#skF_10',D_599) = A_600
      | ~ r2_hidden(D_599,'#skF_7')
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r1_tarski(k2_relat_1('#skF_10'),k1_tarski(A_600)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_840,c_5459])).

tff(c_5580,plain,(
    ! [D_601,A_602] :
      ( k1_funct_1('#skF_10',D_601) = A_602
      | ~ r2_hidden(D_601,'#skF_7')
      | ~ r1_tarski(k2_relat_1('#skF_10'),k1_tarski(A_602)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_92,c_5542])).

tff(c_5706,plain,(
    ! [A_603] :
      ( k1_funct_1('#skF_10','#skF_9') = A_603
      | ~ r1_tarski(k2_relat_1('#skF_10'),k1_tarski(A_603)) ) ),
    inference(resolution,[status(thm)],[c_86,c_5580])).

tff(c_5709,plain,(
    ! [A_603] :
      ( k1_funct_1('#skF_10','#skF_9') = A_603
      | ~ v5_relat_1('#skF_10',k1_tarski(A_603))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_42,c_5706])).

tff(c_5713,plain,(
    ! [A_604] :
      ( k1_funct_1('#skF_10','#skF_9') = A_604
      | ~ v5_relat_1('#skF_10',k1_tarski(A_604)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_5709])).

tff(c_5716,plain,(
    k1_funct_1('#skF_10','#skF_9') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_256,c_5713])).

tff(c_5720,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_5716])).

tff(c_5721,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_839])).

tff(c_126,plain,(
    ! [A_99,B_100] : k1_enumset1(A_99,A_99,B_100) = k2_tarski(A_99,B_100) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10,plain,(
    ! [E_8,B_3,C_4] : r2_hidden(E_8,k1_enumset1(E_8,B_3,C_4)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_153,plain,(
    ! [A_101,B_102] : r2_hidden(A_101,k2_tarski(A_101,B_102)) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_10])).

tff(c_161,plain,(
    ! [A_103] : r2_hidden(A_103,k1_tarski(A_103)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_153])).

tff(c_62,plain,(
    ! [B_64,A_63] :
      ( ~ r1_tarski(B_64,A_63)
      | ~ r2_hidden(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_165,plain,(
    ! [A_103] : ~ r1_tarski(k1_tarski(A_103),A_103) ),
    inference(resolution,[status(thm)],[c_161,c_62])).

tff(c_5754,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_5721,c_165])).

tff(c_5764,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_5754])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:51:17 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.50/2.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.50/2.63  
% 7.50/2.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.50/2.63  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_1 > #skF_5 > #skF_4
% 7.50/2.63  
% 7.50/2.63  %Foreground sorts:
% 7.50/2.63  
% 7.50/2.63  
% 7.50/2.63  %Background operators:
% 7.50/2.63  
% 7.50/2.63  
% 7.50/2.63  %Foreground operators:
% 7.50/2.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.50/2.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.50/2.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.50/2.63  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 7.50/2.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.50/2.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.50/2.63  tff('#skF_7', type, '#skF_7': $i).
% 7.50/2.63  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.50/2.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.50/2.63  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.50/2.63  tff('#skF_10', type, '#skF_10': $i).
% 7.50/2.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.50/2.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.50/2.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.50/2.63  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 7.50/2.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.50/2.63  tff('#skF_9', type, '#skF_9': $i).
% 7.50/2.63  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.50/2.63  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.50/2.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.50/2.63  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.50/2.63  tff('#skF_8', type, '#skF_8': $i).
% 7.50/2.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.50/2.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.50/2.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.50/2.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.50/2.63  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.50/2.63  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 7.50/2.63  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 7.50/2.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.50/2.63  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.50/2.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.50/2.63  
% 7.50/2.64  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.50/2.64  tff(f_128, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 7.50/2.64  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.50/2.64  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.50/2.64  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 7.50/2.64  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.50/2.64  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 7.50/2.64  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.50/2.64  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 7.50/2.64  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 7.50/2.64  tff(f_44, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 7.50/2.64  tff(f_46, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 7.50/2.64  tff(f_42, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 7.50/2.64  tff(f_85, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 7.50/2.64  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.50/2.64  tff(c_84, plain, (k1_funct_1('#skF_10', '#skF_9')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_128])).
% 7.50/2.64  tff(c_88, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8'))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 7.50/2.64  tff(c_247, plain, (![C_131, B_132, A_133]: (v5_relat_1(C_131, B_132) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_133, B_132))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.50/2.64  tff(c_256, plain, (v5_relat_1('#skF_10', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_88, c_247])).
% 7.50/2.64  tff(c_195, plain, (![C_115, A_116, B_117]: (v1_relat_1(C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.50/2.64  tff(c_204, plain, (v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_88, c_195])).
% 7.50/2.64  tff(c_42, plain, (![B_22, A_21]: (r1_tarski(k2_relat_1(B_22), A_21) | ~v5_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.50/2.64  tff(c_86, plain, (r2_hidden('#skF_9', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_128])).
% 7.50/2.64  tff(c_92, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_128])).
% 7.50/2.64  tff(c_90, plain, (v1_funct_2('#skF_10', '#skF_7', k1_tarski('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 7.50/2.64  tff(c_425, plain, (![A_183, B_184, C_185]: (k1_relset_1(A_183, B_184, C_185)=k1_relat_1(C_185) | ~m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1(A_183, B_184))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.50/2.64  tff(c_434, plain, (k1_relset_1('#skF_7', k1_tarski('#skF_8'), '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_88, c_425])).
% 7.50/2.64  tff(c_828, plain, (![B_262, A_263, C_264]: (k1_xboole_0=B_262 | k1_relset_1(A_263, B_262, C_264)=A_263 | ~v1_funct_2(C_264, A_263, B_262) | ~m1_subset_1(C_264, k1_zfmisc_1(k2_zfmisc_1(A_263, B_262))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.50/2.64  tff(c_835, plain, (k1_tarski('#skF_8')=k1_xboole_0 | k1_relset_1('#skF_7', k1_tarski('#skF_8'), '#skF_10')='#skF_7' | ~v1_funct_2('#skF_10', '#skF_7', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_88, c_828])).
% 7.50/2.64  tff(c_839, plain, (k1_tarski('#skF_8')=k1_xboole_0 | k1_relat_1('#skF_10')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_434, c_835])).
% 7.50/2.64  tff(c_840, plain, (k1_relat_1('#skF_10')='#skF_7'), inference(splitLeft, [status(thm)], [c_839])).
% 7.50/2.64  tff(c_38, plain, (![A_19, B_20]: (m1_subset_1(A_19, k1_zfmisc_1(B_20)) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.50/2.64  tff(c_576, plain, (![A_228, D_229]: (r2_hidden(k1_funct_1(A_228, D_229), k2_relat_1(A_228)) | ~r2_hidden(D_229, k1_relat_1(A_228)) | ~v1_funct_1(A_228) | ~v1_relat_1(A_228))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.50/2.64  tff(c_34, plain, (![C_18, A_15, B_16]: (r2_hidden(C_18, A_15) | ~r2_hidden(C_18, B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.50/2.64  tff(c_3110, plain, (![A_458, D_459, A_460]: (r2_hidden(k1_funct_1(A_458, D_459), A_460) | ~m1_subset_1(k2_relat_1(A_458), k1_zfmisc_1(A_460)) | ~r2_hidden(D_459, k1_relat_1(A_458)) | ~v1_funct_1(A_458) | ~v1_relat_1(A_458))), inference(resolution, [status(thm)], [c_576, c_34])).
% 7.50/2.64  tff(c_4690, plain, (![A_546, D_547, B_548]: (r2_hidden(k1_funct_1(A_546, D_547), B_548) | ~r2_hidden(D_547, k1_relat_1(A_546)) | ~v1_funct_1(A_546) | ~v1_relat_1(A_546) | ~r1_tarski(k2_relat_1(A_546), B_548))), inference(resolution, [status(thm)], [c_38, c_3110])).
% 7.50/2.64  tff(c_28, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.50/2.64  tff(c_30, plain, (![A_10, B_11]: (k1_enumset1(A_10, A_10, B_11)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.50/2.64  tff(c_312, plain, (![E_145, C_146, B_147, A_148]: (E_145=C_146 | E_145=B_147 | E_145=A_148 | ~r2_hidden(E_145, k1_enumset1(A_148, B_147, C_146)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.50/2.64  tff(c_506, plain, (![E_215, B_216, A_217]: (E_215=B_216 | E_215=A_217 | E_215=A_217 | ~r2_hidden(E_215, k2_tarski(A_217, B_216)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_312])).
% 7.50/2.64  tff(c_519, plain, (![E_215, A_9]: (E_215=A_9 | E_215=A_9 | E_215=A_9 | ~r2_hidden(E_215, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_506])).
% 7.50/2.64  tff(c_5459, plain, (![A_598, D_599, A_600]: (k1_funct_1(A_598, D_599)=A_600 | ~r2_hidden(D_599, k1_relat_1(A_598)) | ~v1_funct_1(A_598) | ~v1_relat_1(A_598) | ~r1_tarski(k2_relat_1(A_598), k1_tarski(A_600)))), inference(resolution, [status(thm)], [c_4690, c_519])).
% 7.50/2.64  tff(c_5542, plain, (![D_599, A_600]: (k1_funct_1('#skF_10', D_599)=A_600 | ~r2_hidden(D_599, '#skF_7') | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~r1_tarski(k2_relat_1('#skF_10'), k1_tarski(A_600)))), inference(superposition, [status(thm), theory('equality')], [c_840, c_5459])).
% 7.50/2.64  tff(c_5580, plain, (![D_601, A_602]: (k1_funct_1('#skF_10', D_601)=A_602 | ~r2_hidden(D_601, '#skF_7') | ~r1_tarski(k2_relat_1('#skF_10'), k1_tarski(A_602)))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_92, c_5542])).
% 7.50/2.64  tff(c_5706, plain, (![A_603]: (k1_funct_1('#skF_10', '#skF_9')=A_603 | ~r1_tarski(k2_relat_1('#skF_10'), k1_tarski(A_603)))), inference(resolution, [status(thm)], [c_86, c_5580])).
% 7.50/2.64  tff(c_5709, plain, (![A_603]: (k1_funct_1('#skF_10', '#skF_9')=A_603 | ~v5_relat_1('#skF_10', k1_tarski(A_603)) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_42, c_5706])).
% 7.50/2.64  tff(c_5713, plain, (![A_604]: (k1_funct_1('#skF_10', '#skF_9')=A_604 | ~v5_relat_1('#skF_10', k1_tarski(A_604)))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_5709])).
% 7.50/2.64  tff(c_5716, plain, (k1_funct_1('#skF_10', '#skF_9')='#skF_8'), inference(resolution, [status(thm)], [c_256, c_5713])).
% 7.50/2.64  tff(c_5720, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_5716])).
% 7.50/2.64  tff(c_5721, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_839])).
% 7.50/2.64  tff(c_126, plain, (![A_99, B_100]: (k1_enumset1(A_99, A_99, B_100)=k2_tarski(A_99, B_100))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.50/2.64  tff(c_10, plain, (![E_8, B_3, C_4]: (r2_hidden(E_8, k1_enumset1(E_8, B_3, C_4)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.50/2.64  tff(c_153, plain, (![A_101, B_102]: (r2_hidden(A_101, k2_tarski(A_101, B_102)))), inference(superposition, [status(thm), theory('equality')], [c_126, c_10])).
% 7.50/2.64  tff(c_161, plain, (![A_103]: (r2_hidden(A_103, k1_tarski(A_103)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_153])).
% 7.50/2.64  tff(c_62, plain, (![B_64, A_63]: (~r1_tarski(B_64, A_63) | ~r2_hidden(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.50/2.64  tff(c_165, plain, (![A_103]: (~r1_tarski(k1_tarski(A_103), A_103))), inference(resolution, [status(thm)], [c_161, c_62])).
% 7.50/2.64  tff(c_5754, plain, (~r1_tarski(k1_xboole_0, '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_5721, c_165])).
% 7.50/2.64  tff(c_5764, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_5754])).
% 7.50/2.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.50/2.64  
% 7.50/2.64  Inference rules
% 7.50/2.64  ----------------------
% 7.50/2.64  #Ref     : 0
% 7.50/2.64  #Sup     : 1036
% 7.50/2.64  #Fact    : 0
% 7.50/2.64  #Define  : 0
% 7.50/2.64  #Split   : 17
% 7.50/2.64  #Chain   : 0
% 7.50/2.64  #Close   : 0
% 7.50/2.64  
% 7.50/2.64  Ordering : KBO
% 7.50/2.64  
% 7.50/2.64  Simplification rules
% 7.50/2.64  ----------------------
% 7.50/2.64  #Subsume      : 195
% 7.50/2.64  #Demod        : 765
% 7.50/2.64  #Tautology    : 135
% 7.50/2.64  #SimpNegUnit  : 81
% 7.50/2.64  #BackRed      : 309
% 7.50/2.64  
% 7.50/2.64  #Partial instantiations: 0
% 7.50/2.64  #Strategies tried      : 1
% 7.50/2.64  
% 7.50/2.64  Timing (in seconds)
% 7.50/2.64  ----------------------
% 7.50/2.65  Preprocessing        : 0.36
% 7.50/2.65  Parsing              : 0.18
% 7.50/2.65  CNF conversion       : 0.03
% 7.50/2.65  Main loop            : 1.52
% 7.50/2.65  Inferencing          : 0.44
% 7.50/2.65  Reduction            : 0.54
% 7.50/2.65  Demodulation         : 0.35
% 7.50/2.65  BG Simplification    : 0.05
% 7.50/2.65  Subsumption          : 0.37
% 7.50/2.65  Abstraction          : 0.06
% 7.50/2.65  MUC search           : 0.00
% 7.50/2.65  Cooper               : 0.00
% 7.50/2.65  Total                : 1.92
% 7.50/2.65  Index Insertion      : 0.00
% 7.50/2.65  Index Deletion       : 0.00
% 7.50/2.65  Index Matching       : 0.00
% 7.50/2.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
