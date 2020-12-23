%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:46 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   62 (  77 expanded)
%              Number of leaves         :   31 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :  100 ( 152 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_94,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(A,C)
         => r2_relset_1(A,B,k2_partfun1(A,B,D,C),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,A,B)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ! [E] :
                ( r2_hidden(E,A)
               => k1_funct_1(C,E) = k1_funct_1(D,E) )
           => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

tff(c_28,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_45,plain,(
    ! [C_33,A_34,B_35] :
      ( v1_relat_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_54,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_45])).

tff(c_36,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(A_31,B_32)
      | ~ m1_subset_1(A_31,k1_zfmisc_1(B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_44,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_36])).

tff(c_135,plain,(
    ! [A_61,C_62,B_63] :
      ( r1_tarski(k2_zfmisc_1(A_61,C_62),k2_zfmisc_1(B_63,C_62))
      | ~ r1_tarski(A_61,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_495,plain,(
    ! [A_173,B_174,C_175,A_176] :
      ( r1_tarski(A_173,k2_zfmisc_1(B_174,C_175))
      | ~ r1_tarski(A_173,k2_zfmisc_1(A_176,C_175))
      | ~ r1_tarski(A_176,B_174) ) ),
    inference(resolution,[status(thm)],[c_135,c_2])).

tff(c_509,plain,(
    ! [B_179] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(B_179,'#skF_3'))
      | ~ r1_tarski('#skF_2',B_179) ) ),
    inference(resolution,[status(thm)],[c_44,c_495])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_84,plain,(
    ! [C_48,A_49,B_50] :
      ( v4_relat_1(C_48,A_49)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_92,plain,(
    ! [A_7,A_49,B_50] :
      ( v4_relat_1(A_7,A_49)
      | ~ r1_tarski(A_7,k2_zfmisc_1(A_49,B_50)) ) ),
    inference(resolution,[status(thm)],[c_10,c_84])).

tff(c_582,plain,(
    ! [B_180] :
      ( v4_relat_1('#skF_5',B_180)
      | ~ r1_tarski('#skF_2',B_180) ) ),
    inference(resolution,[status(thm)],[c_509,c_92])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( k7_relat_1(B_10,A_9) = B_10
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_585,plain,(
    ! [B_180] :
      ( k7_relat_1('#skF_5',B_180) = '#skF_5'
      | ~ v1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_2',B_180) ) ),
    inference(resolution,[status(thm)],[c_582,c_12])).

tff(c_601,plain,(
    ! [B_182] :
      ( k7_relat_1('#skF_5',B_182) = '#skF_5'
      | ~ r1_tarski('#skF_2',B_182) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_585])).

tff(c_610,plain,(
    k7_relat_1('#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_28,c_601])).

tff(c_34,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_284,plain,(
    ! [A_96,B_97,C_98,D_99] :
      ( k2_partfun1(A_96,B_97,C_98,D_99) = k7_relat_1(C_98,D_99)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97)))
      | ~ v1_funct_1(C_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_289,plain,(
    ! [D_99] :
      ( k2_partfun1('#skF_2','#skF_3','#skF_5',D_99) = k7_relat_1('#skF_5',D_99)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_30,c_284])).

tff(c_293,plain,(
    ! [D_99] : k2_partfun1('#skF_2','#skF_3','#skF_5',D_99) = k7_relat_1('#skF_5',D_99) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_289])).

tff(c_26,plain,(
    ~ r2_relset_1('#skF_2','#skF_3',k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_294,plain,(
    ~ r2_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_26])).

tff(c_611,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_610,c_294])).

tff(c_32,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_22,plain,(
    ! [D_27,A_21,B_22,C_23] :
      ( k1_funct_1(D_27,'#skF_1'(A_21,B_22,C_23,D_27)) != k1_funct_1(C_23,'#skF_1'(A_21,B_22,C_23,D_27))
      | r2_relset_1(A_21,B_22,C_23,D_27)
      | ~ m1_subset_1(D_27,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | ~ v1_funct_2(D_27,A_21,B_22)
      | ~ v1_funct_1(D_27)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | ~ v1_funct_2(C_23,A_21,B_22)
      | ~ v1_funct_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1025,plain,(
    ! [A_207,B_208,C_209] :
      ( r2_relset_1(A_207,B_208,C_209,C_209)
      | ~ m1_subset_1(C_209,k1_zfmisc_1(k2_zfmisc_1(A_207,B_208)))
      | ~ v1_funct_2(C_209,A_207,B_208)
      | ~ v1_funct_1(C_209)
      | ~ m1_subset_1(C_209,k1_zfmisc_1(k2_zfmisc_1(A_207,B_208)))
      | ~ v1_funct_2(C_209,A_207,B_208)
      | ~ v1_funct_1(C_209) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_22])).

tff(c_1030,plain,
    ( r2_relset_1('#skF_2','#skF_3','#skF_5','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_1025])).

tff(c_1034,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_1030])).

tff(c_1036,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_611,c_1034])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:18:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.49  
% 3.20/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.50  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.20/1.50  
% 3.20/1.50  %Foreground sorts:
% 3.20/1.50  
% 3.20/1.50  
% 3.20/1.50  %Background operators:
% 3.20/1.50  
% 3.20/1.50  
% 3.20/1.50  %Foreground operators:
% 3.20/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.20/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.50  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.20/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.20/1.50  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.20/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.20/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.20/1.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.20/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.20/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.20/1.50  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.20/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.20/1.50  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.20/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.20/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.20/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.20/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.50  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.20/1.50  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.20/1.50  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.20/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.20/1.50  
% 3.20/1.51  tff(f_94, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_funct_2)).
% 3.20/1.51  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.20/1.51  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.20/1.51  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 3.20/1.51  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.20/1.51  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.20/1.51  tff(f_47, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.20/1.51  tff(f_63, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.20/1.51  tff(f_83, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_2)).
% 3.20/1.51  tff(c_28, plain, (r1_tarski('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.20/1.51  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.20/1.51  tff(c_45, plain, (![C_33, A_34, B_35]: (v1_relat_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.20/1.51  tff(c_54, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_45])).
% 3.20/1.51  tff(c_36, plain, (![A_31, B_32]: (r1_tarski(A_31, B_32) | ~m1_subset_1(A_31, k1_zfmisc_1(B_32)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.20/1.51  tff(c_44, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_36])).
% 3.20/1.51  tff(c_135, plain, (![A_61, C_62, B_63]: (r1_tarski(k2_zfmisc_1(A_61, C_62), k2_zfmisc_1(B_63, C_62)) | ~r1_tarski(A_61, B_63))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.20/1.51  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.20/1.51  tff(c_495, plain, (![A_173, B_174, C_175, A_176]: (r1_tarski(A_173, k2_zfmisc_1(B_174, C_175)) | ~r1_tarski(A_173, k2_zfmisc_1(A_176, C_175)) | ~r1_tarski(A_176, B_174))), inference(resolution, [status(thm)], [c_135, c_2])).
% 3.20/1.51  tff(c_509, plain, (![B_179]: (r1_tarski('#skF_5', k2_zfmisc_1(B_179, '#skF_3')) | ~r1_tarski('#skF_2', B_179))), inference(resolution, [status(thm)], [c_44, c_495])).
% 3.20/1.51  tff(c_10, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.20/1.51  tff(c_84, plain, (![C_48, A_49, B_50]: (v4_relat_1(C_48, A_49) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.20/1.51  tff(c_92, plain, (![A_7, A_49, B_50]: (v4_relat_1(A_7, A_49) | ~r1_tarski(A_7, k2_zfmisc_1(A_49, B_50)))), inference(resolution, [status(thm)], [c_10, c_84])).
% 3.20/1.51  tff(c_582, plain, (![B_180]: (v4_relat_1('#skF_5', B_180) | ~r1_tarski('#skF_2', B_180))), inference(resolution, [status(thm)], [c_509, c_92])).
% 3.20/1.51  tff(c_12, plain, (![B_10, A_9]: (k7_relat_1(B_10, A_9)=B_10 | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.20/1.51  tff(c_585, plain, (![B_180]: (k7_relat_1('#skF_5', B_180)='#skF_5' | ~v1_relat_1('#skF_5') | ~r1_tarski('#skF_2', B_180))), inference(resolution, [status(thm)], [c_582, c_12])).
% 3.20/1.51  tff(c_601, plain, (![B_182]: (k7_relat_1('#skF_5', B_182)='#skF_5' | ~r1_tarski('#skF_2', B_182))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_585])).
% 3.20/1.51  tff(c_610, plain, (k7_relat_1('#skF_5', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_28, c_601])).
% 3.20/1.51  tff(c_34, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.20/1.51  tff(c_284, plain, (![A_96, B_97, C_98, D_99]: (k2_partfun1(A_96, B_97, C_98, D_99)=k7_relat_1(C_98, D_99) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))) | ~v1_funct_1(C_98))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.20/1.51  tff(c_289, plain, (![D_99]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_99)=k7_relat_1('#skF_5', D_99) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_30, c_284])).
% 3.20/1.51  tff(c_293, plain, (![D_99]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_99)=k7_relat_1('#skF_5', D_99))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_289])).
% 3.20/1.51  tff(c_26, plain, (~r2_relset_1('#skF_2', '#skF_3', k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.20/1.51  tff(c_294, plain, (~r2_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_293, c_26])).
% 3.20/1.51  tff(c_611, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_610, c_294])).
% 3.20/1.51  tff(c_32, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.20/1.51  tff(c_22, plain, (![D_27, A_21, B_22, C_23]: (k1_funct_1(D_27, '#skF_1'(A_21, B_22, C_23, D_27))!=k1_funct_1(C_23, '#skF_1'(A_21, B_22, C_23, D_27)) | r2_relset_1(A_21, B_22, C_23, D_27) | ~m1_subset_1(D_27, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | ~v1_funct_2(D_27, A_21, B_22) | ~v1_funct_1(D_27) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | ~v1_funct_2(C_23, A_21, B_22) | ~v1_funct_1(C_23))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.20/1.51  tff(c_1025, plain, (![A_207, B_208, C_209]: (r2_relset_1(A_207, B_208, C_209, C_209) | ~m1_subset_1(C_209, k1_zfmisc_1(k2_zfmisc_1(A_207, B_208))) | ~v1_funct_2(C_209, A_207, B_208) | ~v1_funct_1(C_209) | ~m1_subset_1(C_209, k1_zfmisc_1(k2_zfmisc_1(A_207, B_208))) | ~v1_funct_2(C_209, A_207, B_208) | ~v1_funct_1(C_209))), inference(reflexivity, [status(thm), theory('equality')], [c_22])).
% 3.20/1.51  tff(c_1030, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_1025])).
% 3.20/1.51  tff(c_1034, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_1030])).
% 3.20/1.51  tff(c_1036, plain, $false, inference(negUnitSimplification, [status(thm)], [c_611, c_1034])).
% 3.20/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.51  
% 3.20/1.51  Inference rules
% 3.20/1.51  ----------------------
% 3.20/1.51  #Ref     : 1
% 3.20/1.51  #Sup     : 255
% 3.20/1.51  #Fact    : 0
% 3.20/1.51  #Define  : 0
% 3.20/1.51  #Split   : 5
% 3.20/1.51  #Chain   : 0
% 3.20/1.51  #Close   : 0
% 3.20/1.51  
% 3.20/1.51  Ordering : KBO
% 3.20/1.51  
% 3.20/1.51  Simplification rules
% 3.20/1.51  ----------------------
% 3.20/1.51  #Subsume      : 53
% 3.20/1.51  #Demod        : 71
% 3.20/1.51  #Tautology    : 60
% 3.20/1.51  #SimpNegUnit  : 2
% 3.20/1.51  #BackRed      : 2
% 3.20/1.51  
% 3.20/1.51  #Partial instantiations: 0
% 3.20/1.51  #Strategies tried      : 1
% 3.20/1.51  
% 3.20/1.51  Timing (in seconds)
% 3.20/1.51  ----------------------
% 3.20/1.51  Preprocessing        : 0.31
% 3.20/1.51  Parsing              : 0.17
% 3.20/1.51  CNF conversion       : 0.02
% 3.20/1.51  Main loop            : 0.43
% 3.20/1.51  Inferencing          : 0.15
% 3.20/1.51  Reduction            : 0.13
% 3.20/1.51  Demodulation         : 0.09
% 3.20/1.51  BG Simplification    : 0.02
% 3.20/1.51  Subsumption          : 0.10
% 3.20/1.51  Abstraction          : 0.02
% 3.20/1.51  MUC search           : 0.00
% 3.20/1.51  Cooper               : 0.00
% 3.20/1.51  Total                : 0.77
% 3.20/1.51  Index Insertion      : 0.00
% 3.20/1.51  Index Deletion       : 0.00
% 3.20/1.52  Index Matching       : 0.00
% 3.20/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
