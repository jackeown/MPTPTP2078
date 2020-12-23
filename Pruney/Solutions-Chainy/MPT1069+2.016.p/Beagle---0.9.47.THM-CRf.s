%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:47 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 391 expanded)
%              Number of leaves         :   42 ( 154 expanded)
%              Depth                    :   17
%              Number of atoms          :  281 (1603 expanded)
%              Number of equality atoms :   58 ( 308 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_183,negated_conjecture,(
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

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_127,axiom,(
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

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_58,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_139,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_158,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).

tff(f_92,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_funct_2)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_58,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_66,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_60,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_180,plain,(
    ! [A_88,B_89,C_90] :
      ( k1_relset_1(A_88,B_89,C_90) = k1_relat_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_193,plain,(
    k1_relset_1('#skF_3','#skF_1','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_180])).

tff(c_56,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relset_1('#skF_3','#skF_1','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_195,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_56])).

tff(c_62,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_606,plain,(
    ! [C_159,D_158,B_156,F_155,A_157,E_160] :
      ( k1_funct_1(k8_funct_2(B_156,C_159,A_157,D_158,E_160),F_155) = k1_funct_1(E_160,k1_funct_1(D_158,F_155))
      | k1_xboole_0 = B_156
      | ~ r1_tarski(k2_relset_1(B_156,C_159,D_158),k1_relset_1(C_159,A_157,E_160))
      | ~ m1_subset_1(F_155,B_156)
      | ~ m1_subset_1(E_160,k1_zfmisc_1(k2_zfmisc_1(C_159,A_157)))
      | ~ v1_funct_1(E_160)
      | ~ m1_subset_1(D_158,k1_zfmisc_1(k2_zfmisc_1(B_156,C_159)))
      | ~ v1_funct_2(D_158,B_156,C_159)
      | ~ v1_funct_1(D_158)
      | v1_xboole_0(C_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_612,plain,(
    ! [B_156,D_158,F_155] :
      ( k1_funct_1(k8_funct_2(B_156,'#skF_3','#skF_1',D_158,'#skF_5'),F_155) = k1_funct_1('#skF_5',k1_funct_1(D_158,F_155))
      | k1_xboole_0 = B_156
      | ~ r1_tarski(k2_relset_1(B_156,'#skF_3',D_158),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(F_155,B_156)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_158,k1_zfmisc_1(k2_zfmisc_1(B_156,'#skF_3')))
      | ~ v1_funct_2(D_158,B_156,'#skF_3')
      | ~ v1_funct_1(D_158)
      | v1_xboole_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_606])).

tff(c_620,plain,(
    ! [B_156,D_158,F_155] :
      ( k1_funct_1(k8_funct_2(B_156,'#skF_3','#skF_1',D_158,'#skF_5'),F_155) = k1_funct_1('#skF_5',k1_funct_1(D_158,F_155))
      | k1_xboole_0 = B_156
      | ~ r1_tarski(k2_relset_1(B_156,'#skF_3',D_158),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(F_155,B_156)
      | ~ m1_subset_1(D_158,k1_zfmisc_1(k2_zfmisc_1(B_156,'#skF_3')))
      | ~ v1_funct_2(D_158,B_156,'#skF_3')
      | ~ v1_funct_1(D_158)
      | v1_xboole_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_612])).

tff(c_650,plain,(
    ! [B_166,D_167,F_168] :
      ( k1_funct_1(k8_funct_2(B_166,'#skF_3','#skF_1',D_167,'#skF_5'),F_168) = k1_funct_1('#skF_5',k1_funct_1(D_167,F_168))
      | k1_xboole_0 = B_166
      | ~ r1_tarski(k2_relset_1(B_166,'#skF_3',D_167),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(F_168,B_166)
      | ~ m1_subset_1(D_167,k1_zfmisc_1(k2_zfmisc_1(B_166,'#skF_3')))
      | ~ v1_funct_2(D_167,B_166,'#skF_3')
      | ~ v1_funct_1(D_167) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_620])).

tff(c_652,plain,(
    ! [F_168] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),F_168) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_168))
      | k1_xboole_0 = '#skF_2'
      | ~ m1_subset_1(F_168,'#skF_2')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_195,c_650])).

tff(c_655,plain,(
    ! [F_168] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),F_168) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_168))
      | k1_xboole_0 = '#skF_2'
      | ~ m1_subset_1(F_168,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_652])).

tff(c_657,plain,(
    ! [F_169] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),F_169) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_169))
      | ~ m1_subset_1(F_169,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_655])).

tff(c_148,plain,(
    ! [C_79,B_80,A_81] :
      ( v5_relat_1(C_79,B_80)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_81,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_161,plain,(
    v5_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_148])).

tff(c_18,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_112,plain,(
    ! [B_71,A_72] :
      ( v1_relat_1(B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_72))
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_115,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_60,c_112])).

tff(c_121,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_115])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_8,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_259,plain,(
    ! [D_110,C_111,B_112,A_113] :
      ( r2_hidden(k1_funct_1(D_110,C_111),B_112)
      | k1_xboole_0 = B_112
      | ~ r2_hidden(C_111,A_113)
      | ~ m1_subset_1(D_110,k1_zfmisc_1(k2_zfmisc_1(A_113,B_112)))
      | ~ v1_funct_2(D_110,A_113,B_112)
      | ~ v1_funct_1(D_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_467,plain,(
    ! [D_145,A_146,B_147,B_148] :
      ( r2_hidden(k1_funct_1(D_145,A_146),B_147)
      | k1_xboole_0 = B_147
      | ~ m1_subset_1(D_145,k1_zfmisc_1(k2_zfmisc_1(B_148,B_147)))
      | ~ v1_funct_2(D_145,B_148,B_147)
      | ~ v1_funct_1(D_145)
      | v1_xboole_0(B_148)
      | ~ m1_subset_1(A_146,B_148) ) ),
    inference(resolution,[status(thm)],[c_14,c_259])).

tff(c_473,plain,(
    ! [A_146] :
      ( r2_hidden(k1_funct_1('#skF_4',A_146),'#skF_3')
      | k1_xboole_0 = '#skF_3'
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_146,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_64,c_467])).

tff(c_483,plain,(
    ! [A_146] :
      ( r2_hidden(k1_funct_1('#skF_4',A_146),'#skF_3')
      | k1_xboole_0 = '#skF_3'
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_146,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_473])).

tff(c_485,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_483])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_491,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_485,c_4])).

tff(c_496,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_491])).

tff(c_498,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_483])).

tff(c_460,plain,(
    ! [B_141,D_142,A_143,C_144] :
      ( k1_xboole_0 = B_141
      | v1_funct_2(D_142,A_143,C_144)
      | ~ r1_tarski(k2_relset_1(A_143,B_141,D_142),C_144)
      | ~ m1_subset_1(D_142,k1_zfmisc_1(k2_zfmisc_1(A_143,B_141)))
      | ~ v1_funct_2(D_142,A_143,B_141)
      | ~ v1_funct_1(D_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_462,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_2',k1_relat_1('#skF_5'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_195,c_460])).

tff(c_465,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_2',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_462])).

tff(c_466,plain,(
    v1_funct_2('#skF_4','#skF_2',k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_465])).

tff(c_497,plain,(
    ! [A_146] :
      ( k1_xboole_0 = '#skF_3'
      | r2_hidden(k1_funct_1('#skF_4',A_146),'#skF_3')
      | ~ m1_subset_1(A_146,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_483])).

tff(c_499,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_497])).

tff(c_517,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_499,c_2])).

tff(c_520,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_517])).

tff(c_522,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_497])).

tff(c_523,plain,(
    ! [B_149,D_150,A_151,C_152] :
      ( k1_xboole_0 = B_149
      | m1_subset_1(D_150,k1_zfmisc_1(k2_zfmisc_1(A_151,C_152)))
      | ~ r1_tarski(k2_relset_1(A_151,B_149,D_150),C_152)
      | ~ m1_subset_1(D_150,k1_zfmisc_1(k2_zfmisc_1(A_151,B_149)))
      | ~ v1_funct_2(D_150,A_151,B_149)
      | ~ v1_funct_1(D_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_525,plain,
    ( k1_xboole_0 = '#skF_3'
    | m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_5'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_195,c_523])).

tff(c_528,plain,
    ( k1_xboole_0 = '#skF_3'
    | m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_525])).

tff(c_529,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_5')))) ),
    inference(negUnitSimplification,[status(thm)],[c_522,c_528])).

tff(c_262,plain,(
    ! [D_110,A_7,B_112,B_8] :
      ( r2_hidden(k1_funct_1(D_110,A_7),B_112)
      | k1_xboole_0 = B_112
      | ~ m1_subset_1(D_110,k1_zfmisc_1(k2_zfmisc_1(B_8,B_112)))
      | ~ v1_funct_2(D_110,B_8,B_112)
      | ~ v1_funct_1(D_110)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(resolution,[status(thm)],[c_14,c_259])).

tff(c_531,plain,(
    ! [A_7] :
      ( r2_hidden(k1_funct_1('#skF_4',A_7),k1_relat_1('#skF_5'))
      | k1_relat_1('#skF_5') = k1_xboole_0
      | ~ v1_funct_2('#skF_4','#skF_2',k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_7,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_529,c_262])).

tff(c_552,plain,(
    ! [A_7] :
      ( r2_hidden(k1_funct_1('#skF_4',A_7),k1_relat_1('#skF_5'))
      | k1_relat_1('#skF_5') = k1_xboole_0
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_7,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_466,c_531])).

tff(c_553,plain,(
    ! [A_7] :
      ( r2_hidden(k1_funct_1('#skF_4',A_7),k1_relat_1('#skF_5'))
      | k1_relat_1('#skF_5') = k1_xboole_0
      | ~ m1_subset_1(A_7,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_498,c_552])).

tff(c_582,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_553])).

tff(c_213,plain,(
    ! [C_101,A_102,B_103] :
      ( ~ v1_xboole_0(C_101)
      | ~ v1_funct_2(C_101,A_102,B_103)
      | ~ v1_funct_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103)))
      | v1_xboole_0(B_103)
      | v1_xboole_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_222,plain,
    ( ~ v1_xboole_0('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_213])).

tff(c_233,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_222])).

tff(c_234,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_233])).

tff(c_236,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_234])).

tff(c_12,plain,(
    ! [B_6,A_4] :
      ( v1_xboole_0(B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_4))
      | ~ v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_546,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_529,c_12])).

tff(c_565,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_236,c_546])).

tff(c_584,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_582,c_565])).

tff(c_594,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8,c_584])).

tff(c_597,plain,(
    ! [A_154] :
      ( r2_hidden(k1_funct_1('#skF_4',A_154),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(A_154,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_553])).

tff(c_34,plain,(
    ! [A_25,B_26,C_28] :
      ( k7_partfun1(A_25,B_26,C_28) = k1_funct_1(B_26,C_28)
      | ~ r2_hidden(C_28,k1_relat_1(B_26))
      | ~ v1_funct_1(B_26)
      | ~ v5_relat_1(B_26,A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_601,plain,(
    ! [A_25,A_154] :
      ( k7_partfun1(A_25,'#skF_5',k1_funct_1('#skF_4',A_154)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',A_154))
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',A_25)
      | ~ v1_relat_1('#skF_5')
      | ~ m1_subset_1(A_154,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_597,c_34])).

tff(c_622,plain,(
    ! [A_161,A_162] :
      ( k7_partfun1(A_161,'#skF_5',k1_funct_1('#skF_4',A_162)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',A_162))
      | ~ v5_relat_1('#skF_5',A_161)
      | ~ m1_subset_1(A_162,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_62,c_601])).

tff(c_52,plain,(
    k7_partfun1('#skF_1','#skF_5',k1_funct_1('#skF_4','#skF_6')) != k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_628,plain,
    ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ v5_relat_1('#skF_5','#skF_1')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_622,c_52])).

tff(c_634,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_161,c_628])).

tff(c_667,plain,(
    ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_657,c_634])).

tff(c_675,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_667])).

tff(c_676,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_465])).

tff(c_694,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_676,c_2])).

tff(c_697,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_694])).

tff(c_698,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_234])).

tff(c_705,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_698,c_4])).

tff(c_710,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_705])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:40:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.24/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.47  
% 3.24/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.47  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.24/1.47  
% 3.24/1.47  %Foreground sorts:
% 3.24/1.47  
% 3.24/1.47  
% 3.24/1.47  %Background operators:
% 3.24/1.47  
% 3.24/1.47  
% 3.24/1.47  %Foreground operators:
% 3.24/1.47  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.24/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.24/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.24/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.24/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.24/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.24/1.47  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 3.24/1.47  tff('#skF_5', type, '#skF_5': $i).
% 3.24/1.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.24/1.47  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 3.24/1.47  tff('#skF_6', type, '#skF_6': $i).
% 3.24/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.24/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.24/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.24/1.47  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.24/1.47  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.24/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.24/1.47  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.24/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.24/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.24/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.24/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.24/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.24/1.47  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.24/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.24/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.24/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.24/1.47  
% 3.24/1.49  tff(f_183, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 3.24/1.49  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.24/1.49  tff(f_127, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 3.24/1.49  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.24/1.49  tff(f_58, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.24/1.49  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.24/1.49  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.24/1.49  tff(f_36, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.24/1.49  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.24/1.49  tff(f_139, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 3.24/1.49  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.24/1.49  tff(f_158, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_2)).
% 3.24/1.49  tff(f_92, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => ((v1_funct_1(C) & ~v1_xboole_0(C)) & v1_funct_2(C, A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc6_funct_2)).
% 3.24/1.49  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.24/1.49  tff(f_103, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 3.24/1.49  tff(c_54, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.24/1.49  tff(c_70, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.24/1.49  tff(c_58, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.24/1.49  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.24/1.49  tff(c_66, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.24/1.49  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.24/1.49  tff(c_60, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.24/1.49  tff(c_180, plain, (![A_88, B_89, C_90]: (k1_relset_1(A_88, B_89, C_90)=k1_relat_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.24/1.49  tff(c_193, plain, (k1_relset_1('#skF_3', '#skF_1', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_180])).
% 3.24/1.49  tff(c_56, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relset_1('#skF_3', '#skF_1', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.24/1.49  tff(c_195, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_193, c_56])).
% 3.24/1.49  tff(c_62, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.24/1.49  tff(c_606, plain, (![C_159, D_158, B_156, F_155, A_157, E_160]: (k1_funct_1(k8_funct_2(B_156, C_159, A_157, D_158, E_160), F_155)=k1_funct_1(E_160, k1_funct_1(D_158, F_155)) | k1_xboole_0=B_156 | ~r1_tarski(k2_relset_1(B_156, C_159, D_158), k1_relset_1(C_159, A_157, E_160)) | ~m1_subset_1(F_155, B_156) | ~m1_subset_1(E_160, k1_zfmisc_1(k2_zfmisc_1(C_159, A_157))) | ~v1_funct_1(E_160) | ~m1_subset_1(D_158, k1_zfmisc_1(k2_zfmisc_1(B_156, C_159))) | ~v1_funct_2(D_158, B_156, C_159) | ~v1_funct_1(D_158) | v1_xboole_0(C_159))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.24/1.49  tff(c_612, plain, (![B_156, D_158, F_155]: (k1_funct_1(k8_funct_2(B_156, '#skF_3', '#skF_1', D_158, '#skF_5'), F_155)=k1_funct_1('#skF_5', k1_funct_1(D_158, F_155)) | k1_xboole_0=B_156 | ~r1_tarski(k2_relset_1(B_156, '#skF_3', D_158), k1_relat_1('#skF_5')) | ~m1_subset_1(F_155, B_156) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_158, k1_zfmisc_1(k2_zfmisc_1(B_156, '#skF_3'))) | ~v1_funct_2(D_158, B_156, '#skF_3') | ~v1_funct_1(D_158) | v1_xboole_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_193, c_606])).
% 3.24/1.49  tff(c_620, plain, (![B_156, D_158, F_155]: (k1_funct_1(k8_funct_2(B_156, '#skF_3', '#skF_1', D_158, '#skF_5'), F_155)=k1_funct_1('#skF_5', k1_funct_1(D_158, F_155)) | k1_xboole_0=B_156 | ~r1_tarski(k2_relset_1(B_156, '#skF_3', D_158), k1_relat_1('#skF_5')) | ~m1_subset_1(F_155, B_156) | ~m1_subset_1(D_158, k1_zfmisc_1(k2_zfmisc_1(B_156, '#skF_3'))) | ~v1_funct_2(D_158, B_156, '#skF_3') | ~v1_funct_1(D_158) | v1_xboole_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_612])).
% 3.24/1.49  tff(c_650, plain, (![B_166, D_167, F_168]: (k1_funct_1(k8_funct_2(B_166, '#skF_3', '#skF_1', D_167, '#skF_5'), F_168)=k1_funct_1('#skF_5', k1_funct_1(D_167, F_168)) | k1_xboole_0=B_166 | ~r1_tarski(k2_relset_1(B_166, '#skF_3', D_167), k1_relat_1('#skF_5')) | ~m1_subset_1(F_168, B_166) | ~m1_subset_1(D_167, k1_zfmisc_1(k2_zfmisc_1(B_166, '#skF_3'))) | ~v1_funct_2(D_167, B_166, '#skF_3') | ~v1_funct_1(D_167))), inference(negUnitSimplification, [status(thm)], [c_70, c_620])).
% 3.24/1.49  tff(c_652, plain, (![F_168]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), F_168)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_168)) | k1_xboole_0='#skF_2' | ~m1_subset_1(F_168, '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_195, c_650])).
% 3.24/1.49  tff(c_655, plain, (![F_168]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), F_168)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_168)) | k1_xboole_0='#skF_2' | ~m1_subset_1(F_168, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_652])).
% 3.24/1.49  tff(c_657, plain, (![F_169]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), F_169)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_169)) | ~m1_subset_1(F_169, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_54, c_655])).
% 3.24/1.49  tff(c_148, plain, (![C_79, B_80, A_81]: (v5_relat_1(C_79, B_80) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_81, B_80))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.24/1.49  tff(c_161, plain, (v5_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_148])).
% 3.24/1.49  tff(c_18, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.24/1.49  tff(c_112, plain, (![B_71, A_72]: (v1_relat_1(B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(A_72)) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.24/1.49  tff(c_115, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_60, c_112])).
% 3.24/1.49  tff(c_121, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_115])).
% 3.24/1.49  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.24/1.49  tff(c_8, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.24/1.49  tff(c_14, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.24/1.49  tff(c_259, plain, (![D_110, C_111, B_112, A_113]: (r2_hidden(k1_funct_1(D_110, C_111), B_112) | k1_xboole_0=B_112 | ~r2_hidden(C_111, A_113) | ~m1_subset_1(D_110, k1_zfmisc_1(k2_zfmisc_1(A_113, B_112))) | ~v1_funct_2(D_110, A_113, B_112) | ~v1_funct_1(D_110))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.24/1.49  tff(c_467, plain, (![D_145, A_146, B_147, B_148]: (r2_hidden(k1_funct_1(D_145, A_146), B_147) | k1_xboole_0=B_147 | ~m1_subset_1(D_145, k1_zfmisc_1(k2_zfmisc_1(B_148, B_147))) | ~v1_funct_2(D_145, B_148, B_147) | ~v1_funct_1(D_145) | v1_xboole_0(B_148) | ~m1_subset_1(A_146, B_148))), inference(resolution, [status(thm)], [c_14, c_259])).
% 3.24/1.49  tff(c_473, plain, (![A_146]: (r2_hidden(k1_funct_1('#skF_4', A_146), '#skF_3') | k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2') | ~m1_subset_1(A_146, '#skF_2'))), inference(resolution, [status(thm)], [c_64, c_467])).
% 3.24/1.49  tff(c_483, plain, (![A_146]: (r2_hidden(k1_funct_1('#skF_4', A_146), '#skF_3') | k1_xboole_0='#skF_3' | v1_xboole_0('#skF_2') | ~m1_subset_1(A_146, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_473])).
% 3.24/1.49  tff(c_485, plain, (v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_483])).
% 3.24/1.49  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.24/1.49  tff(c_491, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_485, c_4])).
% 3.24/1.49  tff(c_496, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_491])).
% 3.24/1.49  tff(c_498, plain, (~v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_483])).
% 3.24/1.49  tff(c_460, plain, (![B_141, D_142, A_143, C_144]: (k1_xboole_0=B_141 | v1_funct_2(D_142, A_143, C_144) | ~r1_tarski(k2_relset_1(A_143, B_141, D_142), C_144) | ~m1_subset_1(D_142, k1_zfmisc_1(k2_zfmisc_1(A_143, B_141))) | ~v1_funct_2(D_142, A_143, B_141) | ~v1_funct_1(D_142))), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.24/1.49  tff(c_462, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_2', k1_relat_1('#skF_5')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_195, c_460])).
% 3.24/1.49  tff(c_465, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_2', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_462])).
% 3.24/1.49  tff(c_466, plain, (v1_funct_2('#skF_4', '#skF_2', k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_465])).
% 3.24/1.49  tff(c_497, plain, (![A_146]: (k1_xboole_0='#skF_3' | r2_hidden(k1_funct_1('#skF_4', A_146), '#skF_3') | ~m1_subset_1(A_146, '#skF_2'))), inference(splitRight, [status(thm)], [c_483])).
% 3.24/1.49  tff(c_499, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_497])).
% 3.24/1.49  tff(c_517, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_499, c_2])).
% 3.24/1.49  tff(c_520, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_517])).
% 3.24/1.49  tff(c_522, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_497])).
% 3.24/1.49  tff(c_523, plain, (![B_149, D_150, A_151, C_152]: (k1_xboole_0=B_149 | m1_subset_1(D_150, k1_zfmisc_1(k2_zfmisc_1(A_151, C_152))) | ~r1_tarski(k2_relset_1(A_151, B_149, D_150), C_152) | ~m1_subset_1(D_150, k1_zfmisc_1(k2_zfmisc_1(A_151, B_149))) | ~v1_funct_2(D_150, A_151, B_149) | ~v1_funct_1(D_150))), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.24/1.49  tff(c_525, plain, (k1_xboole_0='#skF_3' | m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_5')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_195, c_523])).
% 3.24/1.49  tff(c_528, plain, (k1_xboole_0='#skF_3' | m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_525])).
% 3.24/1.49  tff(c_529, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_522, c_528])).
% 3.24/1.49  tff(c_262, plain, (![D_110, A_7, B_112, B_8]: (r2_hidden(k1_funct_1(D_110, A_7), B_112) | k1_xboole_0=B_112 | ~m1_subset_1(D_110, k1_zfmisc_1(k2_zfmisc_1(B_8, B_112))) | ~v1_funct_2(D_110, B_8, B_112) | ~v1_funct_1(D_110) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(resolution, [status(thm)], [c_14, c_259])).
% 3.24/1.49  tff(c_531, plain, (![A_7]: (r2_hidden(k1_funct_1('#skF_4', A_7), k1_relat_1('#skF_5')) | k1_relat_1('#skF_5')=k1_xboole_0 | ~v1_funct_2('#skF_4', '#skF_2', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2') | ~m1_subset_1(A_7, '#skF_2'))), inference(resolution, [status(thm)], [c_529, c_262])).
% 3.24/1.49  tff(c_552, plain, (![A_7]: (r2_hidden(k1_funct_1('#skF_4', A_7), k1_relat_1('#skF_5')) | k1_relat_1('#skF_5')=k1_xboole_0 | v1_xboole_0('#skF_2') | ~m1_subset_1(A_7, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_466, c_531])).
% 3.24/1.49  tff(c_553, plain, (![A_7]: (r2_hidden(k1_funct_1('#skF_4', A_7), k1_relat_1('#skF_5')) | k1_relat_1('#skF_5')=k1_xboole_0 | ~m1_subset_1(A_7, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_498, c_552])).
% 3.24/1.49  tff(c_582, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_553])).
% 3.24/1.49  tff(c_213, plain, (![C_101, A_102, B_103]: (~v1_xboole_0(C_101) | ~v1_funct_2(C_101, A_102, B_103) | ~v1_funct_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))) | v1_xboole_0(B_103) | v1_xboole_0(A_102))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.24/1.49  tff(c_222, plain, (~v1_xboole_0('#skF_4') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_64, c_213])).
% 3.24/1.49  tff(c_233, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_222])).
% 3.24/1.49  tff(c_234, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_70, c_233])).
% 3.24/1.49  tff(c_236, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_234])).
% 3.24/1.49  tff(c_12, plain, (![B_6, A_4]: (v1_xboole_0(B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_4)) | ~v1_xboole_0(A_4))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.24/1.49  tff(c_546, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_529, c_12])).
% 3.24/1.49  tff(c_565, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_236, c_546])).
% 3.24/1.49  tff(c_584, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_582, c_565])).
% 3.24/1.49  tff(c_594, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_8, c_584])).
% 3.24/1.49  tff(c_597, plain, (![A_154]: (r2_hidden(k1_funct_1('#skF_4', A_154), k1_relat_1('#skF_5')) | ~m1_subset_1(A_154, '#skF_2'))), inference(splitRight, [status(thm)], [c_553])).
% 3.24/1.49  tff(c_34, plain, (![A_25, B_26, C_28]: (k7_partfun1(A_25, B_26, C_28)=k1_funct_1(B_26, C_28) | ~r2_hidden(C_28, k1_relat_1(B_26)) | ~v1_funct_1(B_26) | ~v5_relat_1(B_26, A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.24/1.49  tff(c_601, plain, (![A_25, A_154]: (k7_partfun1(A_25, '#skF_5', k1_funct_1('#skF_4', A_154))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', A_154)) | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', A_25) | ~v1_relat_1('#skF_5') | ~m1_subset_1(A_154, '#skF_2'))), inference(resolution, [status(thm)], [c_597, c_34])).
% 3.24/1.49  tff(c_622, plain, (![A_161, A_162]: (k7_partfun1(A_161, '#skF_5', k1_funct_1('#skF_4', A_162))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', A_162)) | ~v5_relat_1('#skF_5', A_161) | ~m1_subset_1(A_162, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_62, c_601])).
% 3.24/1.49  tff(c_52, plain, (k7_partfun1('#skF_1', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))!=k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.24/1.49  tff(c_628, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~v5_relat_1('#skF_5', '#skF_1') | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_622, c_52])).
% 3.24/1.49  tff(c_634, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_161, c_628])).
% 3.24/1.49  tff(c_667, plain, (~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_657, c_634])).
% 3.24/1.49  tff(c_675, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_667])).
% 3.24/1.49  tff(c_676, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_465])).
% 3.24/1.49  tff(c_694, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_676, c_2])).
% 3.24/1.49  tff(c_697, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_694])).
% 3.24/1.49  tff(c_698, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_234])).
% 3.24/1.49  tff(c_705, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_698, c_4])).
% 3.24/1.49  tff(c_710, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_705])).
% 3.24/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.49  
% 3.24/1.49  Inference rules
% 3.24/1.49  ----------------------
% 3.24/1.49  #Ref     : 0
% 3.24/1.49  #Sup     : 114
% 3.24/1.49  #Fact    : 0
% 3.24/1.49  #Define  : 0
% 3.24/1.49  #Split   : 13
% 3.24/1.49  #Chain   : 0
% 3.24/1.49  #Close   : 0
% 3.24/1.49  
% 3.24/1.49  Ordering : KBO
% 3.24/1.49  
% 3.24/1.49  Simplification rules
% 3.24/1.49  ----------------------
% 3.24/1.49  #Subsume      : 5
% 3.24/1.49  #Demod        : 193
% 3.24/1.49  #Tautology    : 52
% 3.24/1.50  #SimpNegUnit  : 20
% 3.24/1.50  #BackRed      : 79
% 3.24/1.50  
% 3.24/1.50  #Partial instantiations: 0
% 3.24/1.50  #Strategies tried      : 1
% 3.24/1.50  
% 3.24/1.50  Timing (in seconds)
% 3.24/1.50  ----------------------
% 3.24/1.50  Preprocessing        : 0.36
% 3.24/1.50  Parsing              : 0.19
% 3.24/1.50  CNF conversion       : 0.03
% 3.24/1.50  Main loop            : 0.36
% 3.24/1.50  Inferencing          : 0.11
% 3.24/1.50  Reduction            : 0.13
% 3.24/1.50  Demodulation         : 0.09
% 3.24/1.50  BG Simplification    : 0.02
% 3.24/1.50  Subsumption          : 0.08
% 3.24/1.50  Abstraction          : 0.02
% 3.24/1.50  MUC search           : 0.00
% 3.24/1.50  Cooper               : 0.00
% 3.24/1.50  Total                : 0.76
% 3.24/1.50  Index Insertion      : 0.00
% 3.24/1.50  Index Deletion       : 0.00
% 3.24/1.50  Index Matching       : 0.00
% 3.24/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
