%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:48 EST 2020

% Result     : Theorem 4.17s
% Output     : CNFRefutation 4.17s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 552 expanded)
%              Number of leaves         :   43 ( 209 expanded)
%              Depth                    :   17
%              Number of atoms          :  305 (1993 expanded)
%              Number of equality atoms :   65 ( 462 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_134,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_99,axiom,(
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

tff(f_146,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_110,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_158,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_81,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_funct_2)).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_56,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_132,plain,(
    ! [A_84,B_85,C_86] :
      ( k1_relset_1(A_84,B_85,C_86) = k1_relat_1(C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_139,plain,(
    k1_relset_1('#skF_3','#skF_1','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_132])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_114,plain,(
    ! [A_81,B_82,C_83] :
      ( k2_relset_1(A_81,B_82,C_83) = k2_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_122,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_114])).

tff(c_54,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relset_1('#skF_3','#skF_1','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_127,plain,(
    r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_3','#skF_1','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_54])).

tff(c_141,plain,(
    r1_tarski(k2_relat_1('#skF_4'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_127])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_498,plain,(
    ! [E_143,A_144,B_142,C_145,D_146,F_147] :
      ( k1_funct_1(k8_funct_2(B_142,C_145,A_144,D_146,E_143),F_147) = k1_funct_1(E_143,k1_funct_1(D_146,F_147))
      | k1_xboole_0 = B_142
      | ~ r1_tarski(k2_relset_1(B_142,C_145,D_146),k1_relset_1(C_145,A_144,E_143))
      | ~ m1_subset_1(F_147,B_142)
      | ~ m1_subset_1(E_143,k1_zfmisc_1(k2_zfmisc_1(C_145,A_144)))
      | ~ v1_funct_1(E_143)
      | ~ m1_subset_1(D_146,k1_zfmisc_1(k2_zfmisc_1(B_142,C_145)))
      | ~ v1_funct_2(D_146,B_142,C_145)
      | ~ v1_funct_1(D_146)
      | v1_xboole_0(C_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_508,plain,(
    ! [A_144,E_143,F_147] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3',A_144,'#skF_4',E_143),F_147) = k1_funct_1(E_143,k1_funct_1('#skF_4',F_147))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_3',A_144,E_143))
      | ~ m1_subset_1(F_147,'#skF_2')
      | ~ m1_subset_1(E_143,k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_144)))
      | ~ v1_funct_1(E_143)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_498])).

tff(c_524,plain,(
    ! [A_144,E_143,F_147] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3',A_144,'#skF_4',E_143),F_147) = k1_funct_1(E_143,k1_funct_1('#skF_4',F_147))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_3',A_144,E_143))
      | ~ m1_subset_1(F_147,'#skF_2')
      | ~ m1_subset_1(E_143,k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_144)))
      | ~ v1_funct_1(E_143)
      | v1_xboole_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_508])).

tff(c_660,plain,(
    ! [A_173,E_174,F_175] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3',A_173,'#skF_4',E_174),F_175) = k1_funct_1(E_174,k1_funct_1('#skF_4',F_175))
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_3',A_173,E_174))
      | ~ m1_subset_1(F_175,'#skF_2')
      | ~ m1_subset_1(E_174,k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_173)))
      | ~ v1_funct_1(E_174) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_52,c_524])).

tff(c_662,plain,(
    ! [F_175] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),F_175) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_175))
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(F_175,'#skF_2')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_660])).

tff(c_664,plain,(
    ! [F_175] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),F_175) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_175))
      | ~ m1_subset_1(F_175,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_141,c_662])).

tff(c_94,plain,(
    ! [C_74,B_75,A_76] :
      ( v5_relat_1(C_74,B_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_76,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_101,plain,(
    v5_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_94])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_76,plain,(
    ! [C_68,A_69,B_70] :
      ( v1_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_84,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_76])).

tff(c_140,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_132])).

tff(c_230,plain,(
    ! [B_107,A_108,C_109] :
      ( k1_xboole_0 = B_107
      | k1_relset_1(A_108,B_107,C_109) = A_108
      | ~ v1_funct_2(C_109,A_108,B_107)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_108,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_239,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_230])).

tff(c_245,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_140,c_239])).

tff(c_246,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_245])).

tff(c_44,plain,(
    ! [B_49,A_48] :
      ( v1_funct_2(B_49,k1_relat_1(B_49),A_48)
      | ~ r1_tarski(k2_relat_1(B_49),A_48)
      | ~ v1_funct_1(B_49)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_258,plain,(
    ! [A_48] :
      ( v1_funct_2('#skF_4','#skF_2',A_48)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_48)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_44])).

tff(c_294,plain,(
    ! [A_113] :
      ( v1_funct_2('#skF_4','#skF_2',A_113)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_66,c_258])).

tff(c_298,plain,(
    v1_funct_2('#skF_4','#skF_2',k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_141,c_294])).

tff(c_83,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_76])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( r2_hidden(A_2,B_3)
      | v1_xboole_0(B_3)
      | ~ m1_subset_1(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_351,plain,(
    ! [A_116,B_117,C_118] :
      ( k7_partfun1(A_116,B_117,C_118) = k1_funct_1(B_117,C_118)
      | ~ r2_hidden(C_118,k1_relat_1(B_117))
      | ~ v1_funct_1(B_117)
      | ~ v5_relat_1(B_117,A_116)
      | ~ v1_relat_1(B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_353,plain,(
    ! [A_116,C_118] :
      ( k7_partfun1(A_116,'#skF_4',C_118) = k1_funct_1('#skF_4',C_118)
      | ~ r2_hidden(C_118,'#skF_2')
      | ~ v1_funct_1('#skF_4')
      | ~ v5_relat_1('#skF_4',A_116)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_351])).

tff(c_379,plain,(
    ! [A_122,C_123] :
      ( k7_partfun1(A_122,'#skF_4',C_123) = k1_funct_1('#skF_4',C_123)
      | ~ r2_hidden(C_123,'#skF_2')
      | ~ v5_relat_1('#skF_4',A_122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_66,c_353])).

tff(c_383,plain,(
    ! [A_122,A_2] :
      ( k7_partfun1(A_122,'#skF_4',A_2) = k1_funct_1('#skF_4',A_2)
      | ~ v5_relat_1('#skF_4',A_122)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_2,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_6,c_379])).

tff(c_384,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_383])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_412,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_384,c_4])).

tff(c_416,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_412])).

tff(c_418,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_383])).

tff(c_42,plain,(
    ! [B_49,A_48] :
      ( m1_subset_1(B_49,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_49),A_48)))
      | ~ r1_tarski(k2_relat_1(B_49),A_48)
      | ~ v1_funct_1(B_49)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_255,plain,(
    ! [A_48] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_48)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_48)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_42])).

tff(c_262,plain,(
    ! [A_48] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_48)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_66,c_255])).

tff(c_470,plain,(
    ! [D_134,C_135,B_136,A_137] :
      ( r2_hidden(k1_funct_1(D_134,C_135),B_136)
      | k1_xboole_0 = B_136
      | ~ r2_hidden(C_135,A_137)
      | ~ m1_subset_1(D_134,k1_zfmisc_1(k2_zfmisc_1(A_137,B_136)))
      | ~ v1_funct_2(D_134,A_137,B_136)
      | ~ v1_funct_1(D_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_557,plain,(
    ! [D_154,A_155,B_156,B_157] :
      ( r2_hidden(k1_funct_1(D_154,A_155),B_156)
      | k1_xboole_0 = B_156
      | ~ m1_subset_1(D_154,k1_zfmisc_1(k2_zfmisc_1(B_157,B_156)))
      | ~ v1_funct_2(D_154,B_157,B_156)
      | ~ v1_funct_1(D_154)
      | v1_xboole_0(B_157)
      | ~ m1_subset_1(A_155,B_157) ) ),
    inference(resolution,[status(thm)],[c_6,c_470])).

tff(c_559,plain,(
    ! [A_155,A_48] :
      ( r2_hidden(k1_funct_1('#skF_4',A_155),A_48)
      | k1_xboole_0 = A_48
      | ~ v1_funct_2('#skF_4','#skF_2',A_48)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_155,'#skF_2')
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_48) ) ),
    inference(resolution,[status(thm)],[c_262,c_557])).

tff(c_568,plain,(
    ! [A_155,A_48] :
      ( r2_hidden(k1_funct_1('#skF_4',A_155),A_48)
      | k1_xboole_0 = A_48
      | ~ v1_funct_2('#skF_4','#skF_2',A_48)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_155,'#skF_2')
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_559])).

tff(c_602,plain,(
    ! [A_159,A_160] :
      ( r2_hidden(k1_funct_1('#skF_4',A_159),A_160)
      | k1_xboole_0 = A_160
      | ~ v1_funct_2('#skF_4','#skF_2',A_160)
      | ~ m1_subset_1(A_159,'#skF_2')
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_160) ) ),
    inference(negUnitSimplification,[status(thm)],[c_418,c_568])).

tff(c_38,plain,(
    ! [A_27,B_28,C_30] :
      ( k7_partfun1(A_27,B_28,C_30) = k1_funct_1(B_28,C_30)
      | ~ r2_hidden(C_30,k1_relat_1(B_28))
      | ~ v1_funct_1(B_28)
      | ~ v5_relat_1(B_28,A_27)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_710,plain,(
    ! [A_187,B_188,A_189] :
      ( k7_partfun1(A_187,B_188,k1_funct_1('#skF_4',A_189)) = k1_funct_1(B_188,k1_funct_1('#skF_4',A_189))
      | ~ v1_funct_1(B_188)
      | ~ v5_relat_1(B_188,A_187)
      | ~ v1_relat_1(B_188)
      | k1_relat_1(B_188) = k1_xboole_0
      | ~ v1_funct_2('#skF_4','#skF_2',k1_relat_1(B_188))
      | ~ m1_subset_1(A_189,'#skF_2')
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relat_1(B_188)) ) ),
    inference(resolution,[status(thm)],[c_602,c_38])).

tff(c_714,plain,(
    ! [A_187,A_189] :
      ( k7_partfun1(A_187,'#skF_5',k1_funct_1('#skF_4',A_189)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',A_189))
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',A_187)
      | ~ v1_relat_1('#skF_5')
      | k1_relat_1('#skF_5') = k1_xboole_0
      | ~ v1_funct_2('#skF_4','#skF_2',k1_relat_1('#skF_5'))
      | ~ m1_subset_1(A_189,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_141,c_710])).

tff(c_720,plain,(
    ! [A_187,A_189] :
      ( k7_partfun1(A_187,'#skF_5',k1_funct_1('#skF_4',A_189)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',A_189))
      | ~ v5_relat_1('#skF_5',A_187)
      | k1_relat_1('#skF_5') = k1_xboole_0
      | ~ m1_subset_1(A_189,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_83,c_60,c_714])).

tff(c_721,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_720])).

tff(c_153,plain,(
    ! [B_93,A_94] :
      ( m1_subset_1(B_93,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_93),A_94)))
      | ~ r1_tarski(k2_relat_1(B_93),A_94)
      | ~ v1_funct_1(B_93)
      | ~ v1_relat_1(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_14,plain,(
    ! [C_13,B_11,A_10] :
      ( v1_xboole_0(C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(B_11,A_10)))
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_201,plain,(
    ! [B_99,A_100] :
      ( v1_xboole_0(B_99)
      | ~ v1_xboole_0(A_100)
      | ~ r1_tarski(k2_relat_1(B_99),A_100)
      | ~ v1_funct_1(B_99)
      | ~ v1_relat_1(B_99) ) ),
    inference(resolution,[status(thm)],[c_153,c_14])).

tff(c_204,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_141,c_201])).

tff(c_207,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_66,c_204])).

tff(c_208,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_207])).

tff(c_729,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_721,c_208])).

tff(c_735,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_729])).

tff(c_738,plain,(
    ! [A_190,A_191] :
      ( k7_partfun1(A_190,'#skF_5',k1_funct_1('#skF_4',A_191)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',A_191))
      | ~ v5_relat_1('#skF_5',A_190)
      | ~ m1_subset_1(A_191,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_720])).

tff(c_50,plain,(
    k7_partfun1('#skF_1','#skF_5',k1_funct_1('#skF_4','#skF_6')) != k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_744,plain,
    ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ v5_relat_1('#skF_5','#skF_1')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_738,c_50])).

tff(c_750,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_101,c_744])).

tff(c_766,plain,(
    ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_664,c_750])).

tff(c_770,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_766])).

tff(c_771,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_245])).

tff(c_779,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_771,c_2])).

tff(c_782,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_779])).

tff(c_783,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_207])).

tff(c_788,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_783,c_4])).

tff(c_798,plain,(
    '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_788,c_52])).

tff(c_1113,plain,(
    ! [C_226,A_227,B_228] :
      ( ~ v1_xboole_0(C_226)
      | ~ v1_funct_2(C_226,A_227,B_228)
      | ~ v1_funct_1(C_226)
      | ~ m1_subset_1(C_226,k1_zfmisc_1(k2_zfmisc_1(A_227,B_228)))
      | v1_xboole_0(B_228)
      | v1_xboole_0(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1125,plain,
    ( ~ v1_xboole_0('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_1113])).

tff(c_1136,plain,
    ( v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_783,c_1125])).

tff(c_1137,plain,(
    v1_xboole_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1136])).

tff(c_796,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_788,c_4])).

tff(c_1140,plain,(
    '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1137,c_796])).

tff(c_1144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_798,c_1140])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:17:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.17/1.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.17/1.85  
% 4.17/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.17/1.85  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.17/1.85  
% 4.17/1.85  %Foreground sorts:
% 4.17/1.85  
% 4.17/1.85  
% 4.17/1.85  %Background operators:
% 4.17/1.85  
% 4.17/1.85  
% 4.17/1.85  %Foreground operators:
% 4.17/1.85  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.17/1.85  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.17/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.17/1.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.17/1.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.17/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.17/1.85  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.17/1.85  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 4.17/1.85  tff('#skF_5', type, '#skF_5': $i).
% 4.17/1.85  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.17/1.85  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 4.17/1.85  tff('#skF_6', type, '#skF_6': $i).
% 4.17/1.85  tff('#skF_2', type, '#skF_2': $i).
% 4.17/1.85  tff('#skF_3', type, '#skF_3': $i).
% 4.17/1.85  tff('#skF_1', type, '#skF_1': $i).
% 4.17/1.85  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.17/1.85  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.17/1.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.17/1.85  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.17/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.17/1.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.17/1.85  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.17/1.85  tff('#skF_4', type, '#skF_4': $i).
% 4.17/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.17/1.85  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.17/1.85  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.17/1.85  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.17/1.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.17/1.85  
% 4.17/1.88  tff(f_183, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t186_funct_2)).
% 4.17/1.88  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.17/1.88  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.17/1.88  tff(f_134, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 4.17/1.88  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.17/1.88  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.17/1.88  tff(f_40, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.17/1.88  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.17/1.88  tff(f_146, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 4.17/1.88  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 4.17/1.88  tff(f_110, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 4.17/1.88  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.17/1.88  tff(f_158, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 4.17/1.88  tff(f_53, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 4.17/1.88  tff(f_81, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => ((v1_funct_1(C) & ~v1_xboole_0(C)) & v1_funct_2(C, A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_funct_2)).
% 4.17/1.88  tff(c_68, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.17/1.88  tff(c_56, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.17/1.88  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.17/1.88  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.17/1.88  tff(c_132, plain, (![A_84, B_85, C_86]: (k1_relset_1(A_84, B_85, C_86)=k1_relat_1(C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.17/1.88  tff(c_139, plain, (k1_relset_1('#skF_3', '#skF_1', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_132])).
% 4.17/1.88  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.17/1.88  tff(c_114, plain, (![A_81, B_82, C_83]: (k2_relset_1(A_81, B_82, C_83)=k2_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.17/1.88  tff(c_122, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_114])).
% 4.17/1.88  tff(c_54, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relset_1('#skF_3', '#skF_1', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.17/1.88  tff(c_127, plain, (r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_3', '#skF_1', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_54])).
% 4.17/1.88  tff(c_141, plain, (r1_tarski(k2_relat_1('#skF_4'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_127])).
% 4.17/1.88  tff(c_52, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.17/1.88  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.17/1.88  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.17/1.88  tff(c_498, plain, (![E_143, A_144, B_142, C_145, D_146, F_147]: (k1_funct_1(k8_funct_2(B_142, C_145, A_144, D_146, E_143), F_147)=k1_funct_1(E_143, k1_funct_1(D_146, F_147)) | k1_xboole_0=B_142 | ~r1_tarski(k2_relset_1(B_142, C_145, D_146), k1_relset_1(C_145, A_144, E_143)) | ~m1_subset_1(F_147, B_142) | ~m1_subset_1(E_143, k1_zfmisc_1(k2_zfmisc_1(C_145, A_144))) | ~v1_funct_1(E_143) | ~m1_subset_1(D_146, k1_zfmisc_1(k2_zfmisc_1(B_142, C_145))) | ~v1_funct_2(D_146, B_142, C_145) | ~v1_funct_1(D_146) | v1_xboole_0(C_145))), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.17/1.88  tff(c_508, plain, (![A_144, E_143, F_147]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', A_144, '#skF_4', E_143), F_147)=k1_funct_1(E_143, k1_funct_1('#skF_4', F_147)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_3', A_144, E_143)) | ~m1_subset_1(F_147, '#skF_2') | ~m1_subset_1(E_143, k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_144))) | ~v1_funct_1(E_143) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_122, c_498])).
% 4.17/1.88  tff(c_524, plain, (![A_144, E_143, F_147]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', A_144, '#skF_4', E_143), F_147)=k1_funct_1(E_143, k1_funct_1('#skF_4', F_147)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_3', A_144, E_143)) | ~m1_subset_1(F_147, '#skF_2') | ~m1_subset_1(E_143, k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_144))) | ~v1_funct_1(E_143) | v1_xboole_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_508])).
% 4.17/1.88  tff(c_660, plain, (![A_173, E_174, F_175]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', A_173, '#skF_4', E_174), F_175)=k1_funct_1(E_174, k1_funct_1('#skF_4', F_175)) | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_3', A_173, E_174)) | ~m1_subset_1(F_175, '#skF_2') | ~m1_subset_1(E_174, k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_173))) | ~v1_funct_1(E_174))), inference(negUnitSimplification, [status(thm)], [c_68, c_52, c_524])).
% 4.17/1.88  tff(c_662, plain, (![F_175]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), F_175)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_175)) | ~r1_tarski(k2_relat_1('#skF_4'), k1_relat_1('#skF_5')) | ~m1_subset_1(F_175, '#skF_2') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_139, c_660])).
% 4.17/1.88  tff(c_664, plain, (![F_175]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), F_175)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_175)) | ~m1_subset_1(F_175, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_141, c_662])).
% 4.17/1.88  tff(c_94, plain, (![C_74, B_75, A_76]: (v5_relat_1(C_74, B_75) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_76, B_75))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.17/1.88  tff(c_101, plain, (v5_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_58, c_94])).
% 4.17/1.88  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.17/1.88  tff(c_76, plain, (![C_68, A_69, B_70]: (v1_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.17/1.88  tff(c_84, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_76])).
% 4.17/1.88  tff(c_140, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_132])).
% 4.17/1.88  tff(c_230, plain, (![B_107, A_108, C_109]: (k1_xboole_0=B_107 | k1_relset_1(A_108, B_107, C_109)=A_108 | ~v1_funct_2(C_109, A_108, B_107) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_108, B_107))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.17/1.88  tff(c_239, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_62, c_230])).
% 4.17/1.88  tff(c_245, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_140, c_239])).
% 4.17/1.88  tff(c_246, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_245])).
% 4.17/1.88  tff(c_44, plain, (![B_49, A_48]: (v1_funct_2(B_49, k1_relat_1(B_49), A_48) | ~r1_tarski(k2_relat_1(B_49), A_48) | ~v1_funct_1(B_49) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.17/1.88  tff(c_258, plain, (![A_48]: (v1_funct_2('#skF_4', '#skF_2', A_48) | ~r1_tarski(k2_relat_1('#skF_4'), A_48) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_246, c_44])).
% 4.17/1.88  tff(c_294, plain, (![A_113]: (v1_funct_2('#skF_4', '#skF_2', A_113) | ~r1_tarski(k2_relat_1('#skF_4'), A_113))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_66, c_258])).
% 4.17/1.88  tff(c_298, plain, (v1_funct_2('#skF_4', '#skF_2', k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_141, c_294])).
% 4.17/1.88  tff(c_83, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_76])).
% 4.17/1.88  tff(c_6, plain, (![A_2, B_3]: (r2_hidden(A_2, B_3) | v1_xboole_0(B_3) | ~m1_subset_1(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.17/1.88  tff(c_351, plain, (![A_116, B_117, C_118]: (k7_partfun1(A_116, B_117, C_118)=k1_funct_1(B_117, C_118) | ~r2_hidden(C_118, k1_relat_1(B_117)) | ~v1_funct_1(B_117) | ~v5_relat_1(B_117, A_116) | ~v1_relat_1(B_117))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.17/1.88  tff(c_353, plain, (![A_116, C_118]: (k7_partfun1(A_116, '#skF_4', C_118)=k1_funct_1('#skF_4', C_118) | ~r2_hidden(C_118, '#skF_2') | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', A_116) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_246, c_351])).
% 4.17/1.88  tff(c_379, plain, (![A_122, C_123]: (k7_partfun1(A_122, '#skF_4', C_123)=k1_funct_1('#skF_4', C_123) | ~r2_hidden(C_123, '#skF_2') | ~v5_relat_1('#skF_4', A_122))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_66, c_353])).
% 4.17/1.88  tff(c_383, plain, (![A_122, A_2]: (k7_partfun1(A_122, '#skF_4', A_2)=k1_funct_1('#skF_4', A_2) | ~v5_relat_1('#skF_4', A_122) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_2, '#skF_2'))), inference(resolution, [status(thm)], [c_6, c_379])).
% 4.17/1.88  tff(c_384, plain, (v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_383])).
% 4.17/1.88  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.17/1.88  tff(c_412, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_384, c_4])).
% 4.17/1.88  tff(c_416, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_412])).
% 4.17/1.88  tff(c_418, plain, (~v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_383])).
% 4.17/1.88  tff(c_42, plain, (![B_49, A_48]: (m1_subset_1(B_49, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_49), A_48))) | ~r1_tarski(k2_relat_1(B_49), A_48) | ~v1_funct_1(B_49) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.17/1.88  tff(c_255, plain, (![A_48]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_48))) | ~r1_tarski(k2_relat_1('#skF_4'), A_48) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_246, c_42])).
% 4.17/1.88  tff(c_262, plain, (![A_48]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_48))) | ~r1_tarski(k2_relat_1('#skF_4'), A_48))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_66, c_255])).
% 4.17/1.88  tff(c_470, plain, (![D_134, C_135, B_136, A_137]: (r2_hidden(k1_funct_1(D_134, C_135), B_136) | k1_xboole_0=B_136 | ~r2_hidden(C_135, A_137) | ~m1_subset_1(D_134, k1_zfmisc_1(k2_zfmisc_1(A_137, B_136))) | ~v1_funct_2(D_134, A_137, B_136) | ~v1_funct_1(D_134))), inference(cnfTransformation, [status(thm)], [f_158])).
% 4.17/1.88  tff(c_557, plain, (![D_154, A_155, B_156, B_157]: (r2_hidden(k1_funct_1(D_154, A_155), B_156) | k1_xboole_0=B_156 | ~m1_subset_1(D_154, k1_zfmisc_1(k2_zfmisc_1(B_157, B_156))) | ~v1_funct_2(D_154, B_157, B_156) | ~v1_funct_1(D_154) | v1_xboole_0(B_157) | ~m1_subset_1(A_155, B_157))), inference(resolution, [status(thm)], [c_6, c_470])).
% 4.17/1.88  tff(c_559, plain, (![A_155, A_48]: (r2_hidden(k1_funct_1('#skF_4', A_155), A_48) | k1_xboole_0=A_48 | ~v1_funct_2('#skF_4', '#skF_2', A_48) | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2') | ~m1_subset_1(A_155, '#skF_2') | ~r1_tarski(k2_relat_1('#skF_4'), A_48))), inference(resolution, [status(thm)], [c_262, c_557])).
% 4.17/1.88  tff(c_568, plain, (![A_155, A_48]: (r2_hidden(k1_funct_1('#skF_4', A_155), A_48) | k1_xboole_0=A_48 | ~v1_funct_2('#skF_4', '#skF_2', A_48) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_155, '#skF_2') | ~r1_tarski(k2_relat_1('#skF_4'), A_48))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_559])).
% 4.17/1.88  tff(c_602, plain, (![A_159, A_160]: (r2_hidden(k1_funct_1('#skF_4', A_159), A_160) | k1_xboole_0=A_160 | ~v1_funct_2('#skF_4', '#skF_2', A_160) | ~m1_subset_1(A_159, '#skF_2') | ~r1_tarski(k2_relat_1('#skF_4'), A_160))), inference(negUnitSimplification, [status(thm)], [c_418, c_568])).
% 4.17/1.88  tff(c_38, plain, (![A_27, B_28, C_30]: (k7_partfun1(A_27, B_28, C_30)=k1_funct_1(B_28, C_30) | ~r2_hidden(C_30, k1_relat_1(B_28)) | ~v1_funct_1(B_28) | ~v5_relat_1(B_28, A_27) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.17/1.88  tff(c_710, plain, (![A_187, B_188, A_189]: (k7_partfun1(A_187, B_188, k1_funct_1('#skF_4', A_189))=k1_funct_1(B_188, k1_funct_1('#skF_4', A_189)) | ~v1_funct_1(B_188) | ~v5_relat_1(B_188, A_187) | ~v1_relat_1(B_188) | k1_relat_1(B_188)=k1_xboole_0 | ~v1_funct_2('#skF_4', '#skF_2', k1_relat_1(B_188)) | ~m1_subset_1(A_189, '#skF_2') | ~r1_tarski(k2_relat_1('#skF_4'), k1_relat_1(B_188)))), inference(resolution, [status(thm)], [c_602, c_38])).
% 4.17/1.88  tff(c_714, plain, (![A_187, A_189]: (k7_partfun1(A_187, '#skF_5', k1_funct_1('#skF_4', A_189))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', A_189)) | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', A_187) | ~v1_relat_1('#skF_5') | k1_relat_1('#skF_5')=k1_xboole_0 | ~v1_funct_2('#skF_4', '#skF_2', k1_relat_1('#skF_5')) | ~m1_subset_1(A_189, '#skF_2'))), inference(resolution, [status(thm)], [c_141, c_710])).
% 4.17/1.88  tff(c_720, plain, (![A_187, A_189]: (k7_partfun1(A_187, '#skF_5', k1_funct_1('#skF_4', A_189))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', A_189)) | ~v5_relat_1('#skF_5', A_187) | k1_relat_1('#skF_5')=k1_xboole_0 | ~m1_subset_1(A_189, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_298, c_83, c_60, c_714])).
% 4.17/1.88  tff(c_721, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_720])).
% 4.17/1.88  tff(c_153, plain, (![B_93, A_94]: (m1_subset_1(B_93, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_93), A_94))) | ~r1_tarski(k2_relat_1(B_93), A_94) | ~v1_funct_1(B_93) | ~v1_relat_1(B_93))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.17/1.88  tff(c_14, plain, (![C_13, B_11, A_10]: (v1_xboole_0(C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(B_11, A_10))) | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.17/1.88  tff(c_201, plain, (![B_99, A_100]: (v1_xboole_0(B_99) | ~v1_xboole_0(A_100) | ~r1_tarski(k2_relat_1(B_99), A_100) | ~v1_funct_1(B_99) | ~v1_relat_1(B_99))), inference(resolution, [status(thm)], [c_153, c_14])).
% 4.17/1.88  tff(c_204, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_141, c_201])).
% 4.17/1.88  tff(c_207, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_66, c_204])).
% 4.17/1.88  tff(c_208, plain, (~v1_xboole_0(k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_207])).
% 4.17/1.88  tff(c_729, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_721, c_208])).
% 4.17/1.88  tff(c_735, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_729])).
% 4.17/1.88  tff(c_738, plain, (![A_190, A_191]: (k7_partfun1(A_190, '#skF_5', k1_funct_1('#skF_4', A_191))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', A_191)) | ~v5_relat_1('#skF_5', A_190) | ~m1_subset_1(A_191, '#skF_2'))), inference(splitRight, [status(thm)], [c_720])).
% 4.17/1.88  tff(c_50, plain, (k7_partfun1('#skF_1', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))!=k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.17/1.88  tff(c_744, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~v5_relat_1('#skF_5', '#skF_1') | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_738, c_50])).
% 4.17/1.88  tff(c_750, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_101, c_744])).
% 4.17/1.88  tff(c_766, plain, (~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_664, c_750])).
% 4.17/1.88  tff(c_770, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_766])).
% 4.17/1.88  tff(c_771, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_245])).
% 4.17/1.88  tff(c_779, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_771, c_2])).
% 4.17/1.88  tff(c_782, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_779])).
% 4.17/1.88  tff(c_783, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_207])).
% 4.17/1.88  tff(c_788, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_783, c_4])).
% 4.17/1.88  tff(c_798, plain, ('#skF_2'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_788, c_52])).
% 4.17/1.88  tff(c_1113, plain, (![C_226, A_227, B_228]: (~v1_xboole_0(C_226) | ~v1_funct_2(C_226, A_227, B_228) | ~v1_funct_1(C_226) | ~m1_subset_1(C_226, k1_zfmisc_1(k2_zfmisc_1(A_227, B_228))) | v1_xboole_0(B_228) | v1_xboole_0(A_227))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.17/1.88  tff(c_1125, plain, (~v1_xboole_0('#skF_4') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_62, c_1113])).
% 4.17/1.88  tff(c_1136, plain, (v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_783, c_1125])).
% 4.17/1.88  tff(c_1137, plain, (v1_xboole_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_68, c_1136])).
% 4.17/1.88  tff(c_796, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_788, c_4])).
% 4.17/1.88  tff(c_1140, plain, ('#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_1137, c_796])).
% 4.17/1.88  tff(c_1144, plain, $false, inference(negUnitSimplification, [status(thm)], [c_798, c_1140])).
% 4.17/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.17/1.88  
% 4.17/1.88  Inference rules
% 4.17/1.88  ----------------------
% 4.17/1.88  #Ref     : 0
% 4.17/1.88  #Sup     : 209
% 4.17/1.88  #Fact    : 0
% 4.17/1.88  #Define  : 0
% 4.17/1.88  #Split   : 15
% 4.17/1.88  #Chain   : 0
% 4.17/1.88  #Close   : 0
% 4.17/1.88  
% 4.17/1.88  Ordering : KBO
% 4.17/1.88  
% 4.17/1.88  Simplification rules
% 4.17/1.88  ----------------------
% 4.17/1.88  #Subsume      : 40
% 4.17/1.88  #Demod        : 265
% 4.17/1.88  #Tautology    : 75
% 4.17/1.88  #SimpNegUnit  : 45
% 4.17/1.88  #BackRed      : 55
% 4.17/1.88  
% 4.17/1.88  #Partial instantiations: 0
% 4.17/1.88  #Strategies tried      : 1
% 4.17/1.88  
% 4.17/1.88  Timing (in seconds)
% 4.17/1.88  ----------------------
% 4.17/1.88  Preprocessing        : 0.40
% 4.17/1.88  Parsing              : 0.22
% 4.17/1.88  CNF conversion       : 0.03
% 4.17/1.88  Main loop            : 0.54
% 4.17/1.88  Inferencing          : 0.19
% 4.17/1.88  Reduction            : 0.18
% 4.17/1.88  Demodulation         : 0.12
% 4.17/1.88  BG Simplification    : 0.03
% 4.17/1.88  Subsumption          : 0.10
% 4.17/1.88  Abstraction          : 0.02
% 4.17/1.88  MUC search           : 0.00
% 4.17/1.88  Cooper               : 0.00
% 4.17/1.88  Total                : 0.99
% 4.17/1.88  Index Insertion      : 0.00
% 4.17/1.88  Index Deletion       : 0.00
% 4.17/1.88  Index Matching       : 0.00
% 4.17/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
