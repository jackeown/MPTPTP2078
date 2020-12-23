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
% DateTime   : Thu Dec  3 10:18:12 EST 2020

% Result     : Theorem 5.71s
% Output     : CNFRefutation 5.99s
% Verified   : 
% Statistics : Number of formulae       :  201 (1340 expanded)
%              Number of leaves         :   47 ( 492 expanded)
%              Depth                    :   22
%              Number of atoms          :  582 (6123 expanded)
%              Number of equality atoms :   94 ( 661 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_208,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C,D] :
                ( ( v1_funct_1(D)
                  & v1_funct_2(D,B,A)
                  & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
               => ! [E] :
                    ( ( v1_funct_1(E)
                      & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C))) )
                   => ! [F] :
                        ( m1_subset_1(F,B)
                       => ( v1_partfun1(E,A)
                         => k3_funct_2(B,C,k8_funct_2(B,A,C,D,E),F) = k7_partfun1(C,E,k3_funct_2(B,A,D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_funct_2)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_181,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_109,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_xboole_0(B) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ~ v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_partfun1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,A)
        & v1_funct_1(C) )
     => ( r2_hidden(B,k1_relat_1(C))
       => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_157,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,A,B)
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
             => ! [D] :
                  ( m1_subset_1(D,A)
                 => k7_partfun1(B,C,D) = k3_funct_2(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_2)).

tff(f_138,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_125,axiom,(
    ! [A,B,C,D,E] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
     => ( v1_funct_1(k8_funct_2(A,B,C,D,E))
        & v1_funct_2(k8_funct_2(A,B,C,D,E),A,C)
        & m1_subset_1(k8_funct_2(A,B,C,D,E),k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_funct_2)).

tff(c_52,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_68,plain,(
    ! [C_105,A_106,B_107] :
      ( v1_relat_1(C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_76,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_68])).

tff(c_92,plain,(
    ! [C_115,B_116,A_117] :
      ( v5_relat_1(C_115,B_116)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_117,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_100,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_92])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k2_relat_1(B_4),A_3)
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_60,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_256,plain,(
    ! [A_143,B_144,C_145] :
      ( k2_relset_1(A_143,B_144,C_145) = k2_relat_1(C_145)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_264,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_256])).

tff(c_818,plain,(
    ! [B_237,A_239,F_238,E_236,D_235,C_240] :
      ( k1_funct_1(k8_funct_2(B_237,C_240,A_239,D_235,E_236),F_238) = k1_funct_1(E_236,k1_funct_1(D_235,F_238))
      | k1_xboole_0 = B_237
      | ~ r1_tarski(k2_relset_1(B_237,C_240,D_235),k1_relset_1(C_240,A_239,E_236))
      | ~ m1_subset_1(F_238,B_237)
      | ~ m1_subset_1(E_236,k1_zfmisc_1(k2_zfmisc_1(C_240,A_239)))
      | ~ v1_funct_1(E_236)
      | ~ m1_subset_1(D_235,k1_zfmisc_1(k2_zfmisc_1(B_237,C_240)))
      | ~ v1_funct_2(D_235,B_237,C_240)
      | ~ v1_funct_1(D_235)
      | v1_xboole_0(C_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_824,plain,(
    ! [A_239,E_236,F_238] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_239,'#skF_4',E_236),F_238) = k1_funct_1(E_236,k1_funct_1('#skF_4',F_238))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_239,E_236))
      | ~ m1_subset_1(F_238,'#skF_2')
      | ~ m1_subset_1(E_236,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_239)))
      | ~ v1_funct_1(E_236)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_818])).

tff(c_834,plain,(
    ! [A_239,E_236,F_238] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_239,'#skF_4',E_236),F_238) = k1_funct_1(E_236,k1_funct_1('#skF_4',F_238))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_239,E_236))
      | ~ m1_subset_1(F_238,'#skF_2')
      | ~ m1_subset_1(E_236,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_239)))
      | ~ v1_funct_1(E_236)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_824])).

tff(c_835,plain,(
    ! [A_239,E_236,F_238] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_239,'#skF_4',E_236),F_238) = k1_funct_1(E_236,k1_funct_1('#skF_4',F_238))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_239,E_236))
      | ~ m1_subset_1(F_238,'#skF_2')
      | ~ m1_subset_1(E_236,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_239)))
      | ~ v1_funct_1(E_236) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_834])).

tff(c_886,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_835])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_888,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_886,c_2])).

tff(c_890,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_888])).

tff(c_892,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_835])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_75,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_68])).

tff(c_50,plain,(
    v1_partfun1('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_83,plain,(
    ! [C_112,A_113,B_114] :
      ( v4_relat_1(C_112,A_113)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_90,plain,(
    v4_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_83])).

tff(c_102,plain,(
    ! [B_119,A_120] :
      ( k1_relat_1(B_119) = A_120
      | ~ v1_partfun1(B_119,A_120)
      | ~ v4_relat_1(B_119,A_120)
      | ~ v1_relat_1(B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_108,plain,
    ( k1_relat_1('#skF_5') = '#skF_1'
    | ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_90,c_102])).

tff(c_114,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_50,c_108])).

tff(c_115,plain,(
    ! [A_121,B_122,C_123] :
      ( k1_relset_1(A_121,B_122,C_123) = k1_relat_1(C_123)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_122,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_115])).

tff(c_133,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_122])).

tff(c_826,plain,(
    ! [B_237,D_235,F_238] :
      ( k1_funct_1(k8_funct_2(B_237,'#skF_1','#skF_3',D_235,'#skF_5'),F_238) = k1_funct_1('#skF_5',k1_funct_1(D_235,F_238))
      | k1_xboole_0 = B_237
      | ~ r1_tarski(k2_relset_1(B_237,'#skF_1',D_235),'#skF_1')
      | ~ m1_subset_1(F_238,B_237)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_235,k1_zfmisc_1(k2_zfmisc_1(B_237,'#skF_1')))
      | ~ v1_funct_2(D_235,B_237,'#skF_1')
      | ~ v1_funct_1(D_235)
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_818])).

tff(c_837,plain,(
    ! [B_237,D_235,F_238] :
      ( k1_funct_1(k8_funct_2(B_237,'#skF_1','#skF_3',D_235,'#skF_5'),F_238) = k1_funct_1('#skF_5',k1_funct_1(D_235,F_238))
      | k1_xboole_0 = B_237
      | ~ r1_tarski(k2_relset_1(B_237,'#skF_1',D_235),'#skF_1')
      | ~ m1_subset_1(F_238,B_237)
      | ~ m1_subset_1(D_235,k1_zfmisc_1(k2_zfmisc_1(B_237,'#skF_1')))
      | ~ v1_funct_2(D_235,B_237,'#skF_1')
      | ~ v1_funct_1(D_235)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_826])).

tff(c_1718,plain,(
    ! [B_341,D_342,F_343] :
      ( k1_funct_1(k8_funct_2(B_341,'#skF_1','#skF_3',D_342,'#skF_5'),F_343) = k1_funct_1('#skF_5',k1_funct_1(D_342,F_343))
      | k1_xboole_0 = B_341
      | ~ r1_tarski(k2_relset_1(B_341,'#skF_1',D_342),'#skF_1')
      | ~ m1_subset_1(F_343,B_341)
      | ~ m1_subset_1(D_342,k1_zfmisc_1(k2_zfmisc_1(B_341,'#skF_1')))
      | ~ v1_funct_2(D_342,B_341,'#skF_1')
      | ~ v1_funct_1(D_342) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_837])).

tff(c_1735,plain,(
    ! [F_343] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_343) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_343))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relset_1('#skF_2','#skF_1','#skF_4'),'#skF_1')
      | ~ m1_subset_1(F_343,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_58,c_1718])).

tff(c_1743,plain,(
    ! [F_343] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_343) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_343))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1')
      | ~ m1_subset_1(F_343,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_264,c_1735])).

tff(c_1744,plain,(
    ! [F_343] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_343) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_343))
      | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1')
      | ~ m1_subset_1(F_343,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_892,c_1743])).

tff(c_1746,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1744])).

tff(c_1749,plain,
    ( ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_1746])).

tff(c_1753,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_100,c_1749])).

tff(c_1754,plain,(
    ! [F_343] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_343) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_343))
      | ~ m1_subset_1(F_343,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_1744])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_288,plain,(
    ! [C_146,A_147,B_148] :
      ( ~ v1_partfun1(C_146,A_147)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_147,B_148)))
      | ~ v1_xboole_0(B_148)
      | v1_xboole_0(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_291,plain,
    ( ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_288])).

tff(c_297,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_291])).

tff(c_298,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_297])).

tff(c_303,plain,(
    ! [C_149,A_150,B_151] :
      ( v1_funct_2(C_149,A_150,B_151)
      | ~ v1_partfun1(C_149,A_150)
      | ~ v1_funct_1(C_149)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_306,plain,
    ( v1_funct_2('#skF_5','#skF_1','#skF_3')
    | ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_303])).

tff(c_312,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_50,c_306])).

tff(c_91,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_83])).

tff(c_105,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ v1_partfun1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_91,c_102])).

tff(c_111,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ v1_partfun1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_105])).

tff(c_142,plain,(
    ~ v1_partfun1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_111])).

tff(c_233,plain,(
    ! [C_140,A_141,B_142] :
      ( v1_partfun1(C_140,A_141)
      | ~ v1_funct_2(C_140,A_141,B_142)
      | ~ v1_funct_1(C_140)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142)))
      | v1_xboole_0(B_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_243,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_233])).

tff(c_251,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_243])).

tff(c_253,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_142,c_251])).

tff(c_254,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_316,plain,(
    ! [C_152,B_153,A_154] :
      ( m1_subset_1(k1_funct_1(C_152,B_153),A_154)
      | ~ r2_hidden(B_153,k1_relat_1(C_152))
      | ~ v1_funct_1(C_152)
      | ~ v5_relat_1(C_152,A_154)
      | ~ v1_relat_1(C_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_318,plain,(
    ! [B_153,A_154] :
      ( m1_subset_1(k1_funct_1('#skF_4',B_153),A_154)
      | ~ r2_hidden(B_153,'#skF_2')
      | ~ v1_funct_1('#skF_4')
      | ~ v5_relat_1('#skF_4',A_154)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_316])).

tff(c_325,plain,(
    ! [B_153,A_154] :
      ( m1_subset_1(k1_funct_1('#skF_4',B_153),A_154)
      | ~ r2_hidden(B_153,'#skF_2')
      | ~ v5_relat_1('#skF_4',A_154) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_62,c_318])).

tff(c_588,plain,(
    ! [A_208,B_209,C_210,D_211] :
      ( k3_funct_2(A_208,B_209,C_210,D_211) = k7_partfun1(B_209,C_210,D_211)
      | ~ m1_subset_1(D_211,A_208)
      | ~ m1_subset_1(C_210,k1_zfmisc_1(k2_zfmisc_1(A_208,B_209)))
      | ~ v1_funct_2(C_210,A_208,B_209)
      | ~ v1_funct_1(C_210)
      | v1_xboole_0(B_209)
      | v1_xboole_0(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_2643,plain,(
    ! [A_443,B_444,C_445,B_446] :
      ( k3_funct_2(A_443,B_444,C_445,k1_funct_1('#skF_4',B_446)) = k7_partfun1(B_444,C_445,k1_funct_1('#skF_4',B_446))
      | ~ m1_subset_1(C_445,k1_zfmisc_1(k2_zfmisc_1(A_443,B_444)))
      | ~ v1_funct_2(C_445,A_443,B_444)
      | ~ v1_funct_1(C_445)
      | v1_xboole_0(B_444)
      | v1_xboole_0(A_443)
      | ~ r2_hidden(B_446,'#skF_2')
      | ~ v5_relat_1('#skF_4',A_443) ) ),
    inference(resolution,[status(thm)],[c_325,c_588])).

tff(c_2664,plain,(
    ! [B_446] :
      ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4',B_446)) = k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4',B_446))
      | ~ v1_funct_2('#skF_5','#skF_1','#skF_3')
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0('#skF_3')
      | v1_xboole_0('#skF_1')
      | ~ r2_hidden(B_446,'#skF_2')
      | ~ v5_relat_1('#skF_4','#skF_1') ) ),
    inference(resolution,[status(thm)],[c_54,c_2643])).

tff(c_2679,plain,(
    ! [B_446] :
      ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4',B_446)) = k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4',B_446))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0('#skF_1')
      | ~ r2_hidden(B_446,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_56,c_312,c_2664])).

tff(c_2685,plain,(
    ! [B_447] :
      ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4',B_447)) = k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4',B_447))
      | ~ r2_hidden(B_447,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_298,c_2679])).

tff(c_471,plain,(
    ! [A_169,B_170,C_171,D_172] :
      ( k3_funct_2(A_169,B_170,C_171,D_172) = k1_funct_1(C_171,D_172)
      | ~ m1_subset_1(D_172,A_169)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(A_169,B_170)))
      | ~ v1_funct_2(C_171,A_169,B_170)
      | ~ v1_funct_1(C_171)
      | v1_xboole_0(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_2460,plain,(
    ! [A_406,B_407,C_408,B_409] :
      ( k3_funct_2(A_406,B_407,C_408,k1_funct_1('#skF_4',B_409)) = k1_funct_1(C_408,k1_funct_1('#skF_4',B_409))
      | ~ m1_subset_1(C_408,k1_zfmisc_1(k2_zfmisc_1(A_406,B_407)))
      | ~ v1_funct_2(C_408,A_406,B_407)
      | ~ v1_funct_1(C_408)
      | v1_xboole_0(A_406)
      | ~ r2_hidden(B_409,'#skF_2')
      | ~ v5_relat_1('#skF_4',A_406) ) ),
    inference(resolution,[status(thm)],[c_325,c_471])).

tff(c_2481,plain,(
    ! [B_409] :
      ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4',B_409)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',B_409))
      | ~ v1_funct_2('#skF_5','#skF_1','#skF_3')
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0('#skF_1')
      | ~ r2_hidden(B_409,'#skF_2')
      | ~ v5_relat_1('#skF_4','#skF_1') ) ),
    inference(resolution,[status(thm)],[c_54,c_2460])).

tff(c_2496,plain,(
    ! [B_409] :
      ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4',B_409)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',B_409))
      | v1_xboole_0('#skF_1')
      | ~ r2_hidden(B_409,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_56,c_312,c_2481])).

tff(c_2497,plain,(
    ! [B_409] :
      ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4',B_409)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',B_409))
      | ~ r2_hidden(B_409,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_2496])).

tff(c_2700,plain,(
    ! [B_448] :
      ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4',B_448)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',B_448))
      | ~ r2_hidden(B_448,'#skF_2')
      | ~ r2_hidden(B_448,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2685,c_2497])).

tff(c_523,plain,(
    ! [E_188,B_191,A_187,D_190,C_189] :
      ( v1_funct_1(k8_funct_2(A_187,B_191,C_189,D_190,E_188))
      | ~ m1_subset_1(E_188,k1_zfmisc_1(k2_zfmisc_1(B_191,C_189)))
      | ~ v1_funct_1(E_188)
      | ~ m1_subset_1(D_190,k1_zfmisc_1(k2_zfmisc_1(A_187,B_191)))
      | ~ v1_funct_2(D_190,A_187,B_191)
      | ~ v1_funct_1(D_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_534,plain,(
    ! [A_187,D_190] :
      ( v1_funct_1(k8_funct_2(A_187,'#skF_1','#skF_3',D_190,'#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_190,k1_zfmisc_1(k2_zfmisc_1(A_187,'#skF_1')))
      | ~ v1_funct_2(D_190,A_187,'#skF_1')
      | ~ v1_funct_1(D_190) ) ),
    inference(resolution,[status(thm)],[c_54,c_523])).

tff(c_546,plain,(
    ! [A_192,D_193] :
      ( v1_funct_1(k8_funct_2(A_192,'#skF_1','#skF_3',D_193,'#skF_5'))
      | ~ m1_subset_1(D_193,k1_zfmisc_1(k2_zfmisc_1(A_192,'#skF_1')))
      | ~ v1_funct_2(D_193,A_192,'#skF_1')
      | ~ v1_funct_1(D_193) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_534])).

tff(c_561,plain,
    ( v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_546])).

tff(c_567,plain,(
    v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_561])).

tff(c_638,plain,(
    ! [D_217,C_216,A_214,B_218,E_215] :
      ( v1_funct_2(k8_funct_2(A_214,B_218,C_216,D_217,E_215),A_214,C_216)
      | ~ m1_subset_1(E_215,k1_zfmisc_1(k2_zfmisc_1(B_218,C_216)))
      | ~ v1_funct_1(E_215)
      | ~ m1_subset_1(D_217,k1_zfmisc_1(k2_zfmisc_1(A_214,B_218)))
      | ~ v1_funct_2(D_217,A_214,B_218)
      | ~ v1_funct_1(D_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_649,plain,(
    ! [A_214,D_217] :
      ( v1_funct_2(k8_funct_2(A_214,'#skF_1','#skF_3',D_217,'#skF_5'),A_214,'#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_217,k1_zfmisc_1(k2_zfmisc_1(A_214,'#skF_1')))
      | ~ v1_funct_2(D_217,A_214,'#skF_1')
      | ~ v1_funct_1(D_217) ) ),
    inference(resolution,[status(thm)],[c_54,c_638])).

tff(c_661,plain,(
    ! [A_219,D_220] :
      ( v1_funct_2(k8_funct_2(A_219,'#skF_1','#skF_3',D_220,'#skF_5'),A_219,'#skF_3')
      | ~ m1_subset_1(D_220,k1_zfmisc_1(k2_zfmisc_1(A_219,'#skF_1')))
      | ~ v1_funct_2(D_220,A_219,'#skF_1')
      | ~ v1_funct_1(D_220) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_649])).

tff(c_672,plain,
    ( v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_661])).

tff(c_678,plain,(
    v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_672])).

tff(c_36,plain,(
    ! [D_36,E_37,A_33,B_34,C_35] :
      ( m1_subset_1(k8_funct_2(A_33,B_34,C_35,D_36,E_37),k1_zfmisc_1(k2_zfmisc_1(A_33,C_35)))
      | ~ m1_subset_1(E_37,k1_zfmisc_1(k2_zfmisc_1(B_34,C_35)))
      | ~ v1_funct_1(E_37)
      | ~ m1_subset_1(D_36,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34)))
      | ~ v1_funct_2(D_36,A_33,B_34)
      | ~ v1_funct_1(D_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_692,plain,(
    ! [C_225,D_226,B_227,A_223,E_224] :
      ( m1_subset_1(k8_funct_2(A_223,B_227,C_225,D_226,E_224),k1_zfmisc_1(k2_zfmisc_1(A_223,C_225)))
      | ~ m1_subset_1(E_224,k1_zfmisc_1(k2_zfmisc_1(B_227,C_225)))
      | ~ v1_funct_1(E_224)
      | ~ m1_subset_1(D_226,k1_zfmisc_1(k2_zfmisc_1(A_223,B_227)))
      | ~ v1_funct_2(D_226,A_223,B_227)
      | ~ v1_funct_1(D_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_12,plain,(
    ! [C_10,A_8,B_9] :
      ( v1_relat_1(C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_765,plain,(
    ! [C_230,A_232,B_228,D_229,E_231] :
      ( v1_relat_1(k8_funct_2(A_232,B_228,C_230,D_229,E_231))
      | ~ m1_subset_1(E_231,k1_zfmisc_1(k2_zfmisc_1(B_228,C_230)))
      | ~ v1_funct_1(E_231)
      | ~ m1_subset_1(D_229,k1_zfmisc_1(k2_zfmisc_1(A_232,B_228)))
      | ~ v1_funct_2(D_229,A_232,B_228)
      | ~ v1_funct_1(D_229) ) ),
    inference(resolution,[status(thm)],[c_692,c_12])).

tff(c_778,plain,(
    ! [A_232,D_229] :
      ( v1_relat_1(k8_funct_2(A_232,'#skF_1','#skF_3',D_229,'#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_229,k1_zfmisc_1(k2_zfmisc_1(A_232,'#skF_1')))
      | ~ v1_funct_2(D_229,A_232,'#skF_1')
      | ~ v1_funct_1(D_229) ) ),
    inference(resolution,[status(thm)],[c_54,c_765])).

tff(c_791,plain,(
    ! [A_233,D_234] :
      ( v1_relat_1(k8_funct_2(A_233,'#skF_1','#skF_3',D_234,'#skF_5'))
      | ~ m1_subset_1(D_234,k1_zfmisc_1(k2_zfmisc_1(A_233,'#skF_1')))
      | ~ v1_funct_2(D_234,A_233,'#skF_1')
      | ~ v1_funct_1(D_234) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_778])).

tff(c_810,plain,
    ( v1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_791])).

tff(c_817,plain,(
    v1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_810])).

tff(c_16,plain,(
    ! [C_13,A_11,B_12] :
      ( v4_relat_1(C_13,A_11)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_941,plain,(
    ! [D_253,B_252,E_255,A_256,C_254] :
      ( v4_relat_1(k8_funct_2(A_256,B_252,C_254,D_253,E_255),A_256)
      | ~ m1_subset_1(E_255,k1_zfmisc_1(k2_zfmisc_1(B_252,C_254)))
      | ~ v1_funct_1(E_255)
      | ~ m1_subset_1(D_253,k1_zfmisc_1(k2_zfmisc_1(A_256,B_252)))
      | ~ v1_funct_2(D_253,A_256,B_252)
      | ~ v1_funct_1(D_253) ) ),
    inference(resolution,[status(thm)],[c_692,c_16])).

tff(c_954,plain,(
    ! [A_256,D_253] :
      ( v4_relat_1(k8_funct_2(A_256,'#skF_1','#skF_3',D_253,'#skF_5'),A_256)
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_253,k1_zfmisc_1(k2_zfmisc_1(A_256,'#skF_1')))
      | ~ v1_funct_2(D_253,A_256,'#skF_1')
      | ~ v1_funct_1(D_253) ) ),
    inference(resolution,[status(thm)],[c_54,c_941])).

tff(c_967,plain,(
    ! [A_257,D_258] :
      ( v4_relat_1(k8_funct_2(A_257,'#skF_1','#skF_3',D_258,'#skF_5'),A_257)
      | ~ m1_subset_1(D_258,k1_zfmisc_1(k2_zfmisc_1(A_257,'#skF_1')))
      | ~ v1_funct_2(D_258,A_257,'#skF_1')
      | ~ v1_funct_1(D_258) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_954])).

tff(c_981,plain,
    ( v4_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_967])).

tff(c_988,plain,(
    v4_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_981])).

tff(c_34,plain,(
    ! [B_32,A_31] :
      ( k1_relat_1(B_32) = A_31
      | ~ v1_partfun1(B_32,A_31)
      | ~ v4_relat_1(B_32,A_31)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_991,plain,
    ( k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) = '#skF_2'
    | ~ v1_partfun1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2')
    | ~ v1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_988,c_34])).

tff(c_994,plain,
    ( k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) = '#skF_2'
    | ~ v1_partfun1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_817,c_991])).

tff(c_995,plain,(
    ~ v1_partfun1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_994])).

tff(c_18,plain,(
    ! [A_14,B_15,C_16] :
      ( k1_relset_1(A_14,B_15,C_16) = k1_relat_1(C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1386,plain,(
    ! [E_328,A_329,C_327,D_326,B_325] :
      ( k1_relset_1(A_329,C_327,k8_funct_2(A_329,B_325,C_327,D_326,E_328)) = k1_relat_1(k8_funct_2(A_329,B_325,C_327,D_326,E_328))
      | ~ m1_subset_1(E_328,k1_zfmisc_1(k2_zfmisc_1(B_325,C_327)))
      | ~ v1_funct_1(E_328)
      | ~ m1_subset_1(D_326,k1_zfmisc_1(k2_zfmisc_1(A_329,B_325)))
      | ~ v1_funct_2(D_326,A_329,B_325)
      | ~ v1_funct_1(D_326) ) ),
    inference(resolution,[status(thm)],[c_692,c_18])).

tff(c_1399,plain,(
    ! [A_329,D_326] :
      ( k1_relset_1(A_329,'#skF_3',k8_funct_2(A_329,'#skF_1','#skF_3',D_326,'#skF_5')) = k1_relat_1(k8_funct_2(A_329,'#skF_1','#skF_3',D_326,'#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_326,k1_zfmisc_1(k2_zfmisc_1(A_329,'#skF_1')))
      | ~ v1_funct_2(D_326,A_329,'#skF_1')
      | ~ v1_funct_1(D_326) ) ),
    inference(resolution,[status(thm)],[c_54,c_1386])).

tff(c_1412,plain,(
    ! [A_330,D_331] :
      ( k1_relset_1(A_330,'#skF_3',k8_funct_2(A_330,'#skF_1','#skF_3',D_331,'#skF_5')) = k1_relat_1(k8_funct_2(A_330,'#skF_1','#skF_3',D_331,'#skF_5'))
      | ~ m1_subset_1(D_331,k1_zfmisc_1(k2_zfmisc_1(A_330,'#skF_1')))
      | ~ v1_funct_2(D_331,A_330,'#skF_1')
      | ~ v1_funct_1(D_331) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1399])).

tff(c_1426,plain,
    ( k1_relset_1('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) = k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_1412])).

tff(c_1433,plain,(
    k1_relset_1('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) = k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1426])).

tff(c_46,plain,(
    ! [A_57,D_67,B_58,E_71,C_59,F_73] :
      ( k1_funct_1(k8_funct_2(B_58,C_59,A_57,D_67,E_71),F_73) = k1_funct_1(E_71,k1_funct_1(D_67,F_73))
      | k1_xboole_0 = B_58
      | ~ r1_tarski(k2_relset_1(B_58,C_59,D_67),k1_relset_1(C_59,A_57,E_71))
      | ~ m1_subset_1(F_73,B_58)
      | ~ m1_subset_1(E_71,k1_zfmisc_1(k2_zfmisc_1(C_59,A_57)))
      | ~ v1_funct_1(E_71)
      | ~ m1_subset_1(D_67,k1_zfmisc_1(k2_zfmisc_1(B_58,C_59)))
      | ~ v1_funct_2(D_67,B_58,C_59)
      | ~ v1_funct_1(D_67)
      | v1_xboole_0(C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_1436,plain,(
    ! [B_58,D_67,F_73] :
      ( k1_funct_1(k8_funct_2(B_58,'#skF_2','#skF_3',D_67,k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')),F_73) = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_funct_1(D_67,F_73))
      | k1_xboole_0 = B_58
      | ~ r1_tarski(k2_relset_1(B_58,'#skF_2',D_67),k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')))
      | ~ m1_subset_1(F_73,B_58)
      | ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_67,k1_zfmisc_1(k2_zfmisc_1(B_58,'#skF_2')))
      | ~ v1_funct_2(D_67,B_58,'#skF_2')
      | ~ v1_funct_1(D_67)
      | v1_xboole_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1433,c_46])).

tff(c_1440,plain,(
    ! [B_58,D_67,F_73] :
      ( k1_funct_1(k8_funct_2(B_58,'#skF_2','#skF_3',D_67,k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')),F_73) = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_funct_1(D_67,F_73))
      | k1_xboole_0 = B_58
      | ~ r1_tarski(k2_relset_1(B_58,'#skF_2',D_67),k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')))
      | ~ m1_subset_1(F_73,B_58)
      | ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ m1_subset_1(D_67,k1_zfmisc_1(k2_zfmisc_1(B_58,'#skF_2')))
      | ~ v1_funct_2(D_67,B_58,'#skF_2')
      | ~ v1_funct_1(D_67)
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_567,c_1436])).

tff(c_1441,plain,(
    ! [B_58,D_67,F_73] :
      ( k1_funct_1(k8_funct_2(B_58,'#skF_2','#skF_3',D_67,k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')),F_73) = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_funct_1(D_67,F_73))
      | k1_xboole_0 = B_58
      | ~ r1_tarski(k2_relset_1(B_58,'#skF_2',D_67),k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')))
      | ~ m1_subset_1(F_73,B_58)
      | ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ m1_subset_1(D_67,k1_zfmisc_1(k2_zfmisc_1(B_58,'#skF_2')))
      | ~ v1_funct_2(D_67,B_58,'#skF_2')
      | ~ v1_funct_1(D_67) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1440])).

tff(c_1443,plain,(
    ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1441])).

tff(c_1446,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_1443])).

tff(c_1450,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_54,c_1446])).

tff(c_1452,plain,(
    m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1441])).

tff(c_28,plain,(
    ! [C_30,A_27,B_28] :
      ( v1_partfun1(C_30,A_27)
      | ~ v1_funct_2(C_30,A_27,B_28)
      | ~ v1_funct_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28)))
      | v1_xboole_0(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1485,plain,
    ( v1_partfun1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2')
    | ~ v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3')
    | ~ v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1452,c_28])).

tff(c_1551,plain,
    ( v1_partfun1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_567,c_678,c_1485])).

tff(c_1553,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_298,c_995,c_1551])).

tff(c_1554,plain,(
    k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_994])).

tff(c_1785,plain,(
    ! [C_349,D_348,A_351,B_347,E_350] :
      ( k1_relset_1(A_351,C_349,k8_funct_2(A_351,B_347,C_349,D_348,E_350)) = k1_relat_1(k8_funct_2(A_351,B_347,C_349,D_348,E_350))
      | ~ m1_subset_1(E_350,k1_zfmisc_1(k2_zfmisc_1(B_347,C_349)))
      | ~ v1_funct_1(E_350)
      | ~ m1_subset_1(D_348,k1_zfmisc_1(k2_zfmisc_1(A_351,B_347)))
      | ~ v1_funct_2(D_348,A_351,B_347)
      | ~ v1_funct_1(D_348) ) ),
    inference(resolution,[status(thm)],[c_692,c_18])).

tff(c_1801,plain,(
    ! [A_351,D_348] :
      ( k1_relset_1(A_351,'#skF_3',k8_funct_2(A_351,'#skF_1','#skF_3',D_348,'#skF_5')) = k1_relat_1(k8_funct_2(A_351,'#skF_1','#skF_3',D_348,'#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_348,k1_zfmisc_1(k2_zfmisc_1(A_351,'#skF_1')))
      | ~ v1_funct_2(D_348,A_351,'#skF_1')
      | ~ v1_funct_1(D_348) ) ),
    inference(resolution,[status(thm)],[c_54,c_1785])).

tff(c_1971,plain,(
    ! [A_357,D_358] :
      ( k1_relset_1(A_357,'#skF_3',k8_funct_2(A_357,'#skF_1','#skF_3',D_358,'#skF_5')) = k1_relat_1(k8_funct_2(A_357,'#skF_1','#skF_3',D_358,'#skF_5'))
      | ~ m1_subset_1(D_358,k1_zfmisc_1(k2_zfmisc_1(A_357,'#skF_1')))
      | ~ v1_funct_2(D_358,A_357,'#skF_1')
      | ~ v1_funct_1(D_358) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1801])).

tff(c_1991,plain,
    ( k1_relset_1('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) = k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_1971])).

tff(c_2000,plain,(
    k1_relset_1('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1554,c_1991])).

tff(c_2003,plain,(
    ! [B_58,D_67,F_73] :
      ( k1_funct_1(k8_funct_2(B_58,'#skF_2','#skF_3',D_67,k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')),F_73) = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_funct_1(D_67,F_73))
      | k1_xboole_0 = B_58
      | ~ r1_tarski(k2_relset_1(B_58,'#skF_2',D_67),'#skF_2')
      | ~ m1_subset_1(F_73,B_58)
      | ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_67,k1_zfmisc_1(k2_zfmisc_1(B_58,'#skF_2')))
      | ~ v1_funct_2(D_67,B_58,'#skF_2')
      | ~ v1_funct_1(D_67)
      | v1_xboole_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2000,c_46])).

tff(c_2007,plain,(
    ! [B_58,D_67,F_73] :
      ( k1_funct_1(k8_funct_2(B_58,'#skF_2','#skF_3',D_67,k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')),F_73) = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_funct_1(D_67,F_73))
      | k1_xboole_0 = B_58
      | ~ r1_tarski(k2_relset_1(B_58,'#skF_2',D_67),'#skF_2')
      | ~ m1_subset_1(F_73,B_58)
      | ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ m1_subset_1(D_67,k1_zfmisc_1(k2_zfmisc_1(B_58,'#skF_2')))
      | ~ v1_funct_2(D_67,B_58,'#skF_2')
      | ~ v1_funct_1(D_67)
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_567,c_2003])).

tff(c_2008,plain,(
    ! [B_58,D_67,F_73] :
      ( k1_funct_1(k8_funct_2(B_58,'#skF_2','#skF_3',D_67,k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')),F_73) = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_funct_1(D_67,F_73))
      | k1_xboole_0 = B_58
      | ~ r1_tarski(k2_relset_1(B_58,'#skF_2',D_67),'#skF_2')
      | ~ m1_subset_1(F_73,B_58)
      | ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ m1_subset_1(D_67,k1_zfmisc_1(k2_zfmisc_1(B_58,'#skF_2')))
      | ~ v1_funct_2(D_67,B_58,'#skF_2')
      | ~ v1_funct_1(D_67) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2007])).

tff(c_2133,plain,(
    ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_2008])).

tff(c_2136,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_2133])).

tff(c_2140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_54,c_2136])).

tff(c_2142,plain,(
    m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2008])).

tff(c_483,plain,(
    ! [B_170,C_171] :
      ( k3_funct_2('#skF_2',B_170,C_171,'#skF_6') = k1_funct_1(C_171,'#skF_6')
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_170)))
      | ~ v1_funct_2(C_171,'#skF_2',B_170)
      | ~ v1_funct_1(C_171)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_52,c_471])).

tff(c_491,plain,(
    ! [B_170,C_171] :
      ( k3_funct_2('#skF_2',B_170,C_171,'#skF_6') = k1_funct_1(C_171,'#skF_6')
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_170)))
      | ~ v1_funct_2(C_171,'#skF_2',B_170)
      | ~ v1_funct_1(C_171) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_483])).

tff(c_2164,plain,
    ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6')
    | ~ v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3')
    | ~ v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_2142,c_491])).

tff(c_2219,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_567,c_678,c_2164])).

tff(c_492,plain,(
    ! [B_173,C_174] :
      ( k3_funct_2('#skF_2',B_173,C_174,'#skF_6') = k1_funct_1(C_174,'#skF_6')
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_173)))
      | ~ v1_funct_2(C_174,'#skF_2',B_173)
      | ~ v1_funct_1(C_174) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_483])).

tff(c_507,plain,
    ( k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_492])).

tff(c_513,plain,(
    k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_507])).

tff(c_48,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_514,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_48])).

tff(c_2242,plain,(
    k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) != k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2219,c_514])).

tff(c_2706,plain,
    ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ r2_hidden('#skF_6','#skF_2')
    | ~ r2_hidden('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2700,c_2242])).

tff(c_2712,plain,(
    ~ r2_hidden('#skF_6','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2706])).

tff(c_2740,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_2712])).

tff(c_2743,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2740])).

tff(c_2745,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2743])).

tff(c_2747,plain,(
    r2_hidden('#skF_6','#skF_2') ),
    inference(splitRight,[status(thm)],[c_2706])).

tff(c_2746,plain,
    ( ~ r2_hidden('#skF_6','#skF_2')
    | k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_2706])).

tff(c_2749,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2747,c_2746])).

tff(c_2752,plain,(
    ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1754,c_2749])).

tff(c_2756,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2752])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:34:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.71/2.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.80/2.08  
% 5.80/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.80/2.08  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.80/2.08  
% 5.80/2.08  %Foreground sorts:
% 5.80/2.08  
% 5.80/2.08  
% 5.80/2.08  %Background operators:
% 5.80/2.08  
% 5.80/2.08  
% 5.80/2.08  %Foreground operators:
% 5.80/2.08  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.80/2.08  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.80/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.80/2.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.80/2.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.80/2.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.80/2.08  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.80/2.08  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 5.80/2.08  tff('#skF_5', type, '#skF_5': $i).
% 5.80/2.08  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.80/2.08  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 5.80/2.08  tff('#skF_6', type, '#skF_6': $i).
% 5.80/2.08  tff('#skF_2', type, '#skF_2': $i).
% 5.80/2.08  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.80/2.08  tff('#skF_3', type, '#skF_3': $i).
% 5.80/2.08  tff('#skF_1', type, '#skF_1': $i).
% 5.80/2.08  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.80/2.08  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.80/2.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.80/2.08  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.80/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.80/2.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.80/2.08  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.80/2.08  tff('#skF_4', type, '#skF_4': $i).
% 5.80/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.80/2.08  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.80/2.08  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.80/2.08  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 5.80/2.08  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.80/2.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.80/2.08  
% 5.99/2.12  tff(f_208, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k7_partfun1(C, E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t193_funct_2)).
% 5.99/2.12  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.99/2.12  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.99/2.12  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 5.99/2.12  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.99/2.12  tff(f_181, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 5.99/2.12  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.99/2.12  tff(f_109, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 5.99/2.12  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.99/2.12  tff(f_32, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 5.99/2.12  tff(f_87, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_xboole_0(B)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_partfun1)).
% 5.99/2.12  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 5.99/2.12  tff(f_101, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 5.99/2.12  tff(f_48, axiom, (![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_1)).
% 5.99/2.12  tff(f_157, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, A) => (k7_partfun1(B, C, D) = k3_funct_2(A, B, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_2)).
% 5.99/2.12  tff(f_138, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 5.99/2.12  tff(f_125, axiom, (![A, B, C, D, E]: (((((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(E)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v1_funct_1(k8_funct_2(A, B, C, D, E)) & v1_funct_2(k8_funct_2(A, B, C, D, E), A, C)) & m1_subset_1(k8_funct_2(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(A, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_funct_2)).
% 5.99/2.12  tff(c_52, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 5.99/2.12  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_208])).
% 5.99/2.12  tff(c_68, plain, (![C_105, A_106, B_107]: (v1_relat_1(C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.99/2.12  tff(c_76, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_68])).
% 5.99/2.12  tff(c_92, plain, (![C_115, B_116, A_117]: (v5_relat_1(C_115, B_116) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_117, B_116))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.99/2.12  tff(c_100, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_58, c_92])).
% 5.99/2.12  tff(c_8, plain, (![B_4, A_3]: (r1_tarski(k2_relat_1(B_4), A_3) | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.99/2.12  tff(c_64, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 5.99/2.12  tff(c_66, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_208])).
% 5.99/2.12  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_208])).
% 5.99/2.12  tff(c_60, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_208])).
% 5.99/2.12  tff(c_256, plain, (![A_143, B_144, C_145]: (k2_relset_1(A_143, B_144, C_145)=k2_relat_1(C_145) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.99/2.12  tff(c_264, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_256])).
% 5.99/2.12  tff(c_818, plain, (![B_237, A_239, F_238, E_236, D_235, C_240]: (k1_funct_1(k8_funct_2(B_237, C_240, A_239, D_235, E_236), F_238)=k1_funct_1(E_236, k1_funct_1(D_235, F_238)) | k1_xboole_0=B_237 | ~r1_tarski(k2_relset_1(B_237, C_240, D_235), k1_relset_1(C_240, A_239, E_236)) | ~m1_subset_1(F_238, B_237) | ~m1_subset_1(E_236, k1_zfmisc_1(k2_zfmisc_1(C_240, A_239))) | ~v1_funct_1(E_236) | ~m1_subset_1(D_235, k1_zfmisc_1(k2_zfmisc_1(B_237, C_240))) | ~v1_funct_2(D_235, B_237, C_240) | ~v1_funct_1(D_235) | v1_xboole_0(C_240))), inference(cnfTransformation, [status(thm)], [f_181])).
% 5.99/2.12  tff(c_824, plain, (![A_239, E_236, F_238]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_239, '#skF_4', E_236), F_238)=k1_funct_1(E_236, k1_funct_1('#skF_4', F_238)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_239, E_236)) | ~m1_subset_1(F_238, '#skF_2') | ~m1_subset_1(E_236, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_239))) | ~v1_funct_1(E_236) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_264, c_818])).
% 5.99/2.12  tff(c_834, plain, (![A_239, E_236, F_238]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_239, '#skF_4', E_236), F_238)=k1_funct_1(E_236, k1_funct_1('#skF_4', F_238)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_239, E_236)) | ~m1_subset_1(F_238, '#skF_2') | ~m1_subset_1(E_236, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_239))) | ~v1_funct_1(E_236) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_824])).
% 5.99/2.12  tff(c_835, plain, (![A_239, E_236, F_238]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_239, '#skF_4', E_236), F_238)=k1_funct_1(E_236, k1_funct_1('#skF_4', F_238)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_239, E_236)) | ~m1_subset_1(F_238, '#skF_2') | ~m1_subset_1(E_236, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_239))) | ~v1_funct_1(E_236))), inference(negUnitSimplification, [status(thm)], [c_66, c_834])).
% 5.99/2.12  tff(c_886, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_835])).
% 5.99/2.12  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.99/2.12  tff(c_888, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_886, c_2])).
% 5.99/2.12  tff(c_890, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_888])).
% 5.99/2.12  tff(c_892, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_835])).
% 5.99/2.12  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_208])).
% 5.99/2.12  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_208])).
% 5.99/2.12  tff(c_75, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_68])).
% 5.99/2.12  tff(c_50, plain, (v1_partfun1('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_208])).
% 5.99/2.12  tff(c_83, plain, (![C_112, A_113, B_114]: (v4_relat_1(C_112, A_113) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.99/2.12  tff(c_90, plain, (v4_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_54, c_83])).
% 5.99/2.12  tff(c_102, plain, (![B_119, A_120]: (k1_relat_1(B_119)=A_120 | ~v1_partfun1(B_119, A_120) | ~v4_relat_1(B_119, A_120) | ~v1_relat_1(B_119))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.99/2.12  tff(c_108, plain, (k1_relat_1('#skF_5')='#skF_1' | ~v1_partfun1('#skF_5', '#skF_1') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_90, c_102])).
% 5.99/2.12  tff(c_114, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_75, c_50, c_108])).
% 5.99/2.12  tff(c_115, plain, (![A_121, B_122, C_123]: (k1_relset_1(A_121, B_122, C_123)=k1_relat_1(C_123) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.99/2.12  tff(c_122, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_115])).
% 5.99/2.12  tff(c_133, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_114, c_122])).
% 5.99/2.12  tff(c_826, plain, (![B_237, D_235, F_238]: (k1_funct_1(k8_funct_2(B_237, '#skF_1', '#skF_3', D_235, '#skF_5'), F_238)=k1_funct_1('#skF_5', k1_funct_1(D_235, F_238)) | k1_xboole_0=B_237 | ~r1_tarski(k2_relset_1(B_237, '#skF_1', D_235), '#skF_1') | ~m1_subset_1(F_238, B_237) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_235, k1_zfmisc_1(k2_zfmisc_1(B_237, '#skF_1'))) | ~v1_funct_2(D_235, B_237, '#skF_1') | ~v1_funct_1(D_235) | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_133, c_818])).
% 5.99/2.12  tff(c_837, plain, (![B_237, D_235, F_238]: (k1_funct_1(k8_funct_2(B_237, '#skF_1', '#skF_3', D_235, '#skF_5'), F_238)=k1_funct_1('#skF_5', k1_funct_1(D_235, F_238)) | k1_xboole_0=B_237 | ~r1_tarski(k2_relset_1(B_237, '#skF_1', D_235), '#skF_1') | ~m1_subset_1(F_238, B_237) | ~m1_subset_1(D_235, k1_zfmisc_1(k2_zfmisc_1(B_237, '#skF_1'))) | ~v1_funct_2(D_235, B_237, '#skF_1') | ~v1_funct_1(D_235) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_826])).
% 5.99/2.12  tff(c_1718, plain, (![B_341, D_342, F_343]: (k1_funct_1(k8_funct_2(B_341, '#skF_1', '#skF_3', D_342, '#skF_5'), F_343)=k1_funct_1('#skF_5', k1_funct_1(D_342, F_343)) | k1_xboole_0=B_341 | ~r1_tarski(k2_relset_1(B_341, '#skF_1', D_342), '#skF_1') | ~m1_subset_1(F_343, B_341) | ~m1_subset_1(D_342, k1_zfmisc_1(k2_zfmisc_1(B_341, '#skF_1'))) | ~v1_funct_2(D_342, B_341, '#skF_1') | ~v1_funct_1(D_342))), inference(negUnitSimplification, [status(thm)], [c_66, c_837])).
% 5.99/2.12  tff(c_1735, plain, (![F_343]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_343)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_343)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relset_1('#skF_2', '#skF_1', '#skF_4'), '#skF_1') | ~m1_subset_1(F_343, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_58, c_1718])).
% 5.99/2.12  tff(c_1743, plain, (![F_343]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_343)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_343)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_1') | ~m1_subset_1(F_343, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_264, c_1735])).
% 5.99/2.12  tff(c_1744, plain, (![F_343]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_343)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_343)) | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_1') | ~m1_subset_1(F_343, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_892, c_1743])).
% 5.99/2.12  tff(c_1746, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(splitLeft, [status(thm)], [c_1744])).
% 5.99/2.12  tff(c_1749, plain, (~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_8, c_1746])).
% 5.99/2.12  tff(c_1753, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_100, c_1749])).
% 5.99/2.12  tff(c_1754, plain, (![F_343]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_343)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_343)) | ~m1_subset_1(F_343, '#skF_2'))), inference(splitRight, [status(thm)], [c_1744])).
% 5.99/2.12  tff(c_4, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.99/2.12  tff(c_288, plain, (![C_146, A_147, B_148]: (~v1_partfun1(C_146, A_147) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_147, B_148))) | ~v1_xboole_0(B_148) | v1_xboole_0(A_147))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.99/2.12  tff(c_291, plain, (~v1_partfun1('#skF_5', '#skF_1') | ~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_54, c_288])).
% 5.99/2.12  tff(c_297, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_291])).
% 5.99/2.12  tff(c_298, plain, (~v1_xboole_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_66, c_297])).
% 5.99/2.12  tff(c_303, plain, (![C_149, A_150, B_151]: (v1_funct_2(C_149, A_150, B_151) | ~v1_partfun1(C_149, A_150) | ~v1_funct_1(C_149) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.99/2.12  tff(c_306, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_partfun1('#skF_5', '#skF_1') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_303])).
% 5.99/2.12  tff(c_312, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_50, c_306])).
% 5.99/2.12  tff(c_91, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_58, c_83])).
% 5.99/2.12  tff(c_105, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v1_partfun1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_91, c_102])).
% 5.99/2.12  tff(c_111, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v1_partfun1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_105])).
% 5.99/2.12  tff(c_142, plain, (~v1_partfun1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_111])).
% 5.99/2.12  tff(c_233, plain, (![C_140, A_141, B_142]: (v1_partfun1(C_140, A_141) | ~v1_funct_2(C_140, A_141, B_142) | ~v1_funct_1(C_140) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))) | v1_xboole_0(B_142))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.99/2.12  tff(c_243, plain, (v1_partfun1('#skF_4', '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_58, c_233])).
% 5.99/2.12  tff(c_251, plain, (v1_partfun1('#skF_4', '#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_243])).
% 5.99/2.12  tff(c_253, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_142, c_251])).
% 5.99/2.12  tff(c_254, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_111])).
% 5.99/2.12  tff(c_316, plain, (![C_152, B_153, A_154]: (m1_subset_1(k1_funct_1(C_152, B_153), A_154) | ~r2_hidden(B_153, k1_relat_1(C_152)) | ~v1_funct_1(C_152) | ~v5_relat_1(C_152, A_154) | ~v1_relat_1(C_152))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.99/2.12  tff(c_318, plain, (![B_153, A_154]: (m1_subset_1(k1_funct_1('#skF_4', B_153), A_154) | ~r2_hidden(B_153, '#skF_2') | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', A_154) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_254, c_316])).
% 5.99/2.12  tff(c_325, plain, (![B_153, A_154]: (m1_subset_1(k1_funct_1('#skF_4', B_153), A_154) | ~r2_hidden(B_153, '#skF_2') | ~v5_relat_1('#skF_4', A_154))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_62, c_318])).
% 5.99/2.12  tff(c_588, plain, (![A_208, B_209, C_210, D_211]: (k3_funct_2(A_208, B_209, C_210, D_211)=k7_partfun1(B_209, C_210, D_211) | ~m1_subset_1(D_211, A_208) | ~m1_subset_1(C_210, k1_zfmisc_1(k2_zfmisc_1(A_208, B_209))) | ~v1_funct_2(C_210, A_208, B_209) | ~v1_funct_1(C_210) | v1_xboole_0(B_209) | v1_xboole_0(A_208))), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.99/2.12  tff(c_2643, plain, (![A_443, B_444, C_445, B_446]: (k3_funct_2(A_443, B_444, C_445, k1_funct_1('#skF_4', B_446))=k7_partfun1(B_444, C_445, k1_funct_1('#skF_4', B_446)) | ~m1_subset_1(C_445, k1_zfmisc_1(k2_zfmisc_1(A_443, B_444))) | ~v1_funct_2(C_445, A_443, B_444) | ~v1_funct_1(C_445) | v1_xboole_0(B_444) | v1_xboole_0(A_443) | ~r2_hidden(B_446, '#skF_2') | ~v5_relat_1('#skF_4', A_443))), inference(resolution, [status(thm)], [c_325, c_588])).
% 5.99/2.12  tff(c_2664, plain, (![B_446]: (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', B_446))=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', B_446)) | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1') | ~r2_hidden(B_446, '#skF_2') | ~v5_relat_1('#skF_4', '#skF_1'))), inference(resolution, [status(thm)], [c_54, c_2643])).
% 5.99/2.12  tff(c_2679, plain, (![B_446]: (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', B_446))=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', B_446)) | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1') | ~r2_hidden(B_446, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_56, c_312, c_2664])).
% 5.99/2.12  tff(c_2685, plain, (![B_447]: (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', B_447))=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', B_447)) | ~r2_hidden(B_447, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_66, c_298, c_2679])).
% 5.99/2.12  tff(c_471, plain, (![A_169, B_170, C_171, D_172]: (k3_funct_2(A_169, B_170, C_171, D_172)=k1_funct_1(C_171, D_172) | ~m1_subset_1(D_172, A_169) | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(A_169, B_170))) | ~v1_funct_2(C_171, A_169, B_170) | ~v1_funct_1(C_171) | v1_xboole_0(A_169))), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.99/2.12  tff(c_2460, plain, (![A_406, B_407, C_408, B_409]: (k3_funct_2(A_406, B_407, C_408, k1_funct_1('#skF_4', B_409))=k1_funct_1(C_408, k1_funct_1('#skF_4', B_409)) | ~m1_subset_1(C_408, k1_zfmisc_1(k2_zfmisc_1(A_406, B_407))) | ~v1_funct_2(C_408, A_406, B_407) | ~v1_funct_1(C_408) | v1_xboole_0(A_406) | ~r2_hidden(B_409, '#skF_2') | ~v5_relat_1('#skF_4', A_406))), inference(resolution, [status(thm)], [c_325, c_471])).
% 5.99/2.12  tff(c_2481, plain, (![B_409]: (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', B_409))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', B_409)) | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_1') | ~r2_hidden(B_409, '#skF_2') | ~v5_relat_1('#skF_4', '#skF_1'))), inference(resolution, [status(thm)], [c_54, c_2460])).
% 5.99/2.12  tff(c_2496, plain, (![B_409]: (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', B_409))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', B_409)) | v1_xboole_0('#skF_1') | ~r2_hidden(B_409, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_56, c_312, c_2481])).
% 5.99/2.12  tff(c_2497, plain, (![B_409]: (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', B_409))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', B_409)) | ~r2_hidden(B_409, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_66, c_2496])).
% 5.99/2.12  tff(c_2700, plain, (![B_448]: (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', B_448))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', B_448)) | ~r2_hidden(B_448, '#skF_2') | ~r2_hidden(B_448, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2685, c_2497])).
% 5.99/2.12  tff(c_523, plain, (![E_188, B_191, A_187, D_190, C_189]: (v1_funct_1(k8_funct_2(A_187, B_191, C_189, D_190, E_188)) | ~m1_subset_1(E_188, k1_zfmisc_1(k2_zfmisc_1(B_191, C_189))) | ~v1_funct_1(E_188) | ~m1_subset_1(D_190, k1_zfmisc_1(k2_zfmisc_1(A_187, B_191))) | ~v1_funct_2(D_190, A_187, B_191) | ~v1_funct_1(D_190))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.99/2.12  tff(c_534, plain, (![A_187, D_190]: (v1_funct_1(k8_funct_2(A_187, '#skF_1', '#skF_3', D_190, '#skF_5')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_190, k1_zfmisc_1(k2_zfmisc_1(A_187, '#skF_1'))) | ~v1_funct_2(D_190, A_187, '#skF_1') | ~v1_funct_1(D_190))), inference(resolution, [status(thm)], [c_54, c_523])).
% 5.99/2.12  tff(c_546, plain, (![A_192, D_193]: (v1_funct_1(k8_funct_2(A_192, '#skF_1', '#skF_3', D_193, '#skF_5')) | ~m1_subset_1(D_193, k1_zfmisc_1(k2_zfmisc_1(A_192, '#skF_1'))) | ~v1_funct_2(D_193, A_192, '#skF_1') | ~v1_funct_1(D_193))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_534])).
% 5.99/2.12  tff(c_561, plain, (v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_546])).
% 5.99/2.12  tff(c_567, plain, (v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_561])).
% 5.99/2.12  tff(c_638, plain, (![D_217, C_216, A_214, B_218, E_215]: (v1_funct_2(k8_funct_2(A_214, B_218, C_216, D_217, E_215), A_214, C_216) | ~m1_subset_1(E_215, k1_zfmisc_1(k2_zfmisc_1(B_218, C_216))) | ~v1_funct_1(E_215) | ~m1_subset_1(D_217, k1_zfmisc_1(k2_zfmisc_1(A_214, B_218))) | ~v1_funct_2(D_217, A_214, B_218) | ~v1_funct_1(D_217))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.99/2.12  tff(c_649, plain, (![A_214, D_217]: (v1_funct_2(k8_funct_2(A_214, '#skF_1', '#skF_3', D_217, '#skF_5'), A_214, '#skF_3') | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_217, k1_zfmisc_1(k2_zfmisc_1(A_214, '#skF_1'))) | ~v1_funct_2(D_217, A_214, '#skF_1') | ~v1_funct_1(D_217))), inference(resolution, [status(thm)], [c_54, c_638])).
% 5.99/2.12  tff(c_661, plain, (![A_219, D_220]: (v1_funct_2(k8_funct_2(A_219, '#skF_1', '#skF_3', D_220, '#skF_5'), A_219, '#skF_3') | ~m1_subset_1(D_220, k1_zfmisc_1(k2_zfmisc_1(A_219, '#skF_1'))) | ~v1_funct_2(D_220, A_219, '#skF_1') | ~v1_funct_1(D_220))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_649])).
% 5.99/2.12  tff(c_672, plain, (v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_661])).
% 5.99/2.12  tff(c_678, plain, (v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_672])).
% 5.99/2.12  tff(c_36, plain, (![D_36, E_37, A_33, B_34, C_35]: (m1_subset_1(k8_funct_2(A_33, B_34, C_35, D_36, E_37), k1_zfmisc_1(k2_zfmisc_1(A_33, C_35))) | ~m1_subset_1(E_37, k1_zfmisc_1(k2_zfmisc_1(B_34, C_35))) | ~v1_funct_1(E_37) | ~m1_subset_1(D_36, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))) | ~v1_funct_2(D_36, A_33, B_34) | ~v1_funct_1(D_36))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.99/2.12  tff(c_692, plain, (![C_225, D_226, B_227, A_223, E_224]: (m1_subset_1(k8_funct_2(A_223, B_227, C_225, D_226, E_224), k1_zfmisc_1(k2_zfmisc_1(A_223, C_225))) | ~m1_subset_1(E_224, k1_zfmisc_1(k2_zfmisc_1(B_227, C_225))) | ~v1_funct_1(E_224) | ~m1_subset_1(D_226, k1_zfmisc_1(k2_zfmisc_1(A_223, B_227))) | ~v1_funct_2(D_226, A_223, B_227) | ~v1_funct_1(D_226))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.99/2.12  tff(c_12, plain, (![C_10, A_8, B_9]: (v1_relat_1(C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.99/2.12  tff(c_765, plain, (![C_230, A_232, B_228, D_229, E_231]: (v1_relat_1(k8_funct_2(A_232, B_228, C_230, D_229, E_231)) | ~m1_subset_1(E_231, k1_zfmisc_1(k2_zfmisc_1(B_228, C_230))) | ~v1_funct_1(E_231) | ~m1_subset_1(D_229, k1_zfmisc_1(k2_zfmisc_1(A_232, B_228))) | ~v1_funct_2(D_229, A_232, B_228) | ~v1_funct_1(D_229))), inference(resolution, [status(thm)], [c_692, c_12])).
% 5.99/2.12  tff(c_778, plain, (![A_232, D_229]: (v1_relat_1(k8_funct_2(A_232, '#skF_1', '#skF_3', D_229, '#skF_5')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_229, k1_zfmisc_1(k2_zfmisc_1(A_232, '#skF_1'))) | ~v1_funct_2(D_229, A_232, '#skF_1') | ~v1_funct_1(D_229))), inference(resolution, [status(thm)], [c_54, c_765])).
% 5.99/2.12  tff(c_791, plain, (![A_233, D_234]: (v1_relat_1(k8_funct_2(A_233, '#skF_1', '#skF_3', D_234, '#skF_5')) | ~m1_subset_1(D_234, k1_zfmisc_1(k2_zfmisc_1(A_233, '#skF_1'))) | ~v1_funct_2(D_234, A_233, '#skF_1') | ~v1_funct_1(D_234))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_778])).
% 5.99/2.12  tff(c_810, plain, (v1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_791])).
% 5.99/2.12  tff(c_817, plain, (v1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_810])).
% 5.99/2.12  tff(c_16, plain, (![C_13, A_11, B_12]: (v4_relat_1(C_13, A_11) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.99/2.12  tff(c_941, plain, (![D_253, B_252, E_255, A_256, C_254]: (v4_relat_1(k8_funct_2(A_256, B_252, C_254, D_253, E_255), A_256) | ~m1_subset_1(E_255, k1_zfmisc_1(k2_zfmisc_1(B_252, C_254))) | ~v1_funct_1(E_255) | ~m1_subset_1(D_253, k1_zfmisc_1(k2_zfmisc_1(A_256, B_252))) | ~v1_funct_2(D_253, A_256, B_252) | ~v1_funct_1(D_253))), inference(resolution, [status(thm)], [c_692, c_16])).
% 5.99/2.12  tff(c_954, plain, (![A_256, D_253]: (v4_relat_1(k8_funct_2(A_256, '#skF_1', '#skF_3', D_253, '#skF_5'), A_256) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_253, k1_zfmisc_1(k2_zfmisc_1(A_256, '#skF_1'))) | ~v1_funct_2(D_253, A_256, '#skF_1') | ~v1_funct_1(D_253))), inference(resolution, [status(thm)], [c_54, c_941])).
% 5.99/2.12  tff(c_967, plain, (![A_257, D_258]: (v4_relat_1(k8_funct_2(A_257, '#skF_1', '#skF_3', D_258, '#skF_5'), A_257) | ~m1_subset_1(D_258, k1_zfmisc_1(k2_zfmisc_1(A_257, '#skF_1'))) | ~v1_funct_2(D_258, A_257, '#skF_1') | ~v1_funct_1(D_258))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_954])).
% 5.99/2.12  tff(c_981, plain, (v4_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_967])).
% 5.99/2.12  tff(c_988, plain, (v4_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_981])).
% 5.99/2.12  tff(c_34, plain, (![B_32, A_31]: (k1_relat_1(B_32)=A_31 | ~v1_partfun1(B_32, A_31) | ~v4_relat_1(B_32, A_31) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.99/2.12  tff(c_991, plain, (k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))='#skF_2' | ~v1_partfun1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2') | ~v1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_988, c_34])).
% 5.99/2.12  tff(c_994, plain, (k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))='#skF_2' | ~v1_partfun1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_817, c_991])).
% 5.99/2.12  tff(c_995, plain, (~v1_partfun1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2')), inference(splitLeft, [status(thm)], [c_994])).
% 5.99/2.12  tff(c_18, plain, (![A_14, B_15, C_16]: (k1_relset_1(A_14, B_15, C_16)=k1_relat_1(C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.99/2.12  tff(c_1386, plain, (![E_328, A_329, C_327, D_326, B_325]: (k1_relset_1(A_329, C_327, k8_funct_2(A_329, B_325, C_327, D_326, E_328))=k1_relat_1(k8_funct_2(A_329, B_325, C_327, D_326, E_328)) | ~m1_subset_1(E_328, k1_zfmisc_1(k2_zfmisc_1(B_325, C_327))) | ~v1_funct_1(E_328) | ~m1_subset_1(D_326, k1_zfmisc_1(k2_zfmisc_1(A_329, B_325))) | ~v1_funct_2(D_326, A_329, B_325) | ~v1_funct_1(D_326))), inference(resolution, [status(thm)], [c_692, c_18])).
% 5.99/2.12  tff(c_1399, plain, (![A_329, D_326]: (k1_relset_1(A_329, '#skF_3', k8_funct_2(A_329, '#skF_1', '#skF_3', D_326, '#skF_5'))=k1_relat_1(k8_funct_2(A_329, '#skF_1', '#skF_3', D_326, '#skF_5')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_326, k1_zfmisc_1(k2_zfmisc_1(A_329, '#skF_1'))) | ~v1_funct_2(D_326, A_329, '#skF_1') | ~v1_funct_1(D_326))), inference(resolution, [status(thm)], [c_54, c_1386])).
% 5.99/2.12  tff(c_1412, plain, (![A_330, D_331]: (k1_relset_1(A_330, '#skF_3', k8_funct_2(A_330, '#skF_1', '#skF_3', D_331, '#skF_5'))=k1_relat_1(k8_funct_2(A_330, '#skF_1', '#skF_3', D_331, '#skF_5')) | ~m1_subset_1(D_331, k1_zfmisc_1(k2_zfmisc_1(A_330, '#skF_1'))) | ~v1_funct_2(D_331, A_330, '#skF_1') | ~v1_funct_1(D_331))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1399])).
% 5.99/2.12  tff(c_1426, plain, (k1_relset_1('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))=k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_1412])).
% 5.99/2.12  tff(c_1433, plain, (k1_relset_1('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))=k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1426])).
% 5.99/2.12  tff(c_46, plain, (![A_57, D_67, B_58, E_71, C_59, F_73]: (k1_funct_1(k8_funct_2(B_58, C_59, A_57, D_67, E_71), F_73)=k1_funct_1(E_71, k1_funct_1(D_67, F_73)) | k1_xboole_0=B_58 | ~r1_tarski(k2_relset_1(B_58, C_59, D_67), k1_relset_1(C_59, A_57, E_71)) | ~m1_subset_1(F_73, B_58) | ~m1_subset_1(E_71, k1_zfmisc_1(k2_zfmisc_1(C_59, A_57))) | ~v1_funct_1(E_71) | ~m1_subset_1(D_67, k1_zfmisc_1(k2_zfmisc_1(B_58, C_59))) | ~v1_funct_2(D_67, B_58, C_59) | ~v1_funct_1(D_67) | v1_xboole_0(C_59))), inference(cnfTransformation, [status(thm)], [f_181])).
% 5.99/2.12  tff(c_1436, plain, (![B_58, D_67, F_73]: (k1_funct_1(k8_funct_2(B_58, '#skF_2', '#skF_3', D_67, k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')), F_73)=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_funct_1(D_67, F_73)) | k1_xboole_0=B_58 | ~r1_tarski(k2_relset_1(B_58, '#skF_2', D_67), k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(F_73, B_58) | ~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_67, k1_zfmisc_1(k2_zfmisc_1(B_58, '#skF_2'))) | ~v1_funct_2(D_67, B_58, '#skF_2') | ~v1_funct_1(D_67) | v1_xboole_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1433, c_46])).
% 5.99/2.12  tff(c_1440, plain, (![B_58, D_67, F_73]: (k1_funct_1(k8_funct_2(B_58, '#skF_2', '#skF_3', D_67, k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')), F_73)=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_funct_1(D_67, F_73)) | k1_xboole_0=B_58 | ~r1_tarski(k2_relset_1(B_58, '#skF_2', D_67), k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(F_73, B_58) | ~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1(D_67, k1_zfmisc_1(k2_zfmisc_1(B_58, '#skF_2'))) | ~v1_funct_2(D_67, B_58, '#skF_2') | ~v1_funct_1(D_67) | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_567, c_1436])).
% 5.99/2.12  tff(c_1441, plain, (![B_58, D_67, F_73]: (k1_funct_1(k8_funct_2(B_58, '#skF_2', '#skF_3', D_67, k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')), F_73)=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_funct_1(D_67, F_73)) | k1_xboole_0=B_58 | ~r1_tarski(k2_relset_1(B_58, '#skF_2', D_67), k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(F_73, B_58) | ~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1(D_67, k1_zfmisc_1(k2_zfmisc_1(B_58, '#skF_2'))) | ~v1_funct_2(D_67, B_58, '#skF_2') | ~v1_funct_1(D_67))), inference(negUnitSimplification, [status(thm)], [c_64, c_1440])).
% 5.99/2.12  tff(c_1443, plain, (~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_1441])).
% 5.99/2.12  tff(c_1446, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_1443])).
% 5.99/2.12  tff(c_1450, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_54, c_1446])).
% 5.99/2.12  tff(c_1452, plain, (m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_1441])).
% 5.99/2.12  tff(c_28, plain, (![C_30, A_27, B_28]: (v1_partfun1(C_30, A_27) | ~v1_funct_2(C_30, A_27, B_28) | ~v1_funct_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))) | v1_xboole_0(B_28))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.99/2.12  tff(c_1485, plain, (v1_partfun1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2') | ~v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3') | ~v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_1452, c_28])).
% 5.99/2.12  tff(c_1551, plain, (v1_partfun1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_567, c_678, c_1485])).
% 5.99/2.12  tff(c_1553, plain, $false, inference(negUnitSimplification, [status(thm)], [c_298, c_995, c_1551])).
% 5.99/2.12  tff(c_1554, plain, (k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))='#skF_2'), inference(splitRight, [status(thm)], [c_994])).
% 5.99/2.12  tff(c_1785, plain, (![C_349, D_348, A_351, B_347, E_350]: (k1_relset_1(A_351, C_349, k8_funct_2(A_351, B_347, C_349, D_348, E_350))=k1_relat_1(k8_funct_2(A_351, B_347, C_349, D_348, E_350)) | ~m1_subset_1(E_350, k1_zfmisc_1(k2_zfmisc_1(B_347, C_349))) | ~v1_funct_1(E_350) | ~m1_subset_1(D_348, k1_zfmisc_1(k2_zfmisc_1(A_351, B_347))) | ~v1_funct_2(D_348, A_351, B_347) | ~v1_funct_1(D_348))), inference(resolution, [status(thm)], [c_692, c_18])).
% 5.99/2.12  tff(c_1801, plain, (![A_351, D_348]: (k1_relset_1(A_351, '#skF_3', k8_funct_2(A_351, '#skF_1', '#skF_3', D_348, '#skF_5'))=k1_relat_1(k8_funct_2(A_351, '#skF_1', '#skF_3', D_348, '#skF_5')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_348, k1_zfmisc_1(k2_zfmisc_1(A_351, '#skF_1'))) | ~v1_funct_2(D_348, A_351, '#skF_1') | ~v1_funct_1(D_348))), inference(resolution, [status(thm)], [c_54, c_1785])).
% 5.99/2.12  tff(c_1971, plain, (![A_357, D_358]: (k1_relset_1(A_357, '#skF_3', k8_funct_2(A_357, '#skF_1', '#skF_3', D_358, '#skF_5'))=k1_relat_1(k8_funct_2(A_357, '#skF_1', '#skF_3', D_358, '#skF_5')) | ~m1_subset_1(D_358, k1_zfmisc_1(k2_zfmisc_1(A_357, '#skF_1'))) | ~v1_funct_2(D_358, A_357, '#skF_1') | ~v1_funct_1(D_358))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1801])).
% 5.99/2.12  tff(c_1991, plain, (k1_relset_1('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))=k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_1971])).
% 5.99/2.12  tff(c_2000, plain, (k1_relset_1('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1554, c_1991])).
% 5.99/2.12  tff(c_2003, plain, (![B_58, D_67, F_73]: (k1_funct_1(k8_funct_2(B_58, '#skF_2', '#skF_3', D_67, k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')), F_73)=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_funct_1(D_67, F_73)) | k1_xboole_0=B_58 | ~r1_tarski(k2_relset_1(B_58, '#skF_2', D_67), '#skF_2') | ~m1_subset_1(F_73, B_58) | ~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_67, k1_zfmisc_1(k2_zfmisc_1(B_58, '#skF_2'))) | ~v1_funct_2(D_67, B_58, '#skF_2') | ~v1_funct_1(D_67) | v1_xboole_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2000, c_46])).
% 5.99/2.12  tff(c_2007, plain, (![B_58, D_67, F_73]: (k1_funct_1(k8_funct_2(B_58, '#skF_2', '#skF_3', D_67, k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')), F_73)=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_funct_1(D_67, F_73)) | k1_xboole_0=B_58 | ~r1_tarski(k2_relset_1(B_58, '#skF_2', D_67), '#skF_2') | ~m1_subset_1(F_73, B_58) | ~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1(D_67, k1_zfmisc_1(k2_zfmisc_1(B_58, '#skF_2'))) | ~v1_funct_2(D_67, B_58, '#skF_2') | ~v1_funct_1(D_67) | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_567, c_2003])).
% 5.99/2.12  tff(c_2008, plain, (![B_58, D_67, F_73]: (k1_funct_1(k8_funct_2(B_58, '#skF_2', '#skF_3', D_67, k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')), F_73)=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_funct_1(D_67, F_73)) | k1_xboole_0=B_58 | ~r1_tarski(k2_relset_1(B_58, '#skF_2', D_67), '#skF_2') | ~m1_subset_1(F_73, B_58) | ~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1(D_67, k1_zfmisc_1(k2_zfmisc_1(B_58, '#skF_2'))) | ~v1_funct_2(D_67, B_58, '#skF_2') | ~v1_funct_1(D_67))), inference(negUnitSimplification, [status(thm)], [c_64, c_2007])).
% 5.99/2.12  tff(c_2133, plain, (~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_2008])).
% 5.99/2.12  tff(c_2136, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_2133])).
% 5.99/2.12  tff(c_2140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_54, c_2136])).
% 5.99/2.12  tff(c_2142, plain, (m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_2008])).
% 5.99/2.12  tff(c_483, plain, (![B_170, C_171]: (k3_funct_2('#skF_2', B_170, C_171, '#skF_6')=k1_funct_1(C_171, '#skF_6') | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_170))) | ~v1_funct_2(C_171, '#skF_2', B_170) | ~v1_funct_1(C_171) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_52, c_471])).
% 5.99/2.12  tff(c_491, plain, (![B_170, C_171]: (k3_funct_2('#skF_2', B_170, C_171, '#skF_6')=k1_funct_1(C_171, '#skF_6') | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_170))) | ~v1_funct_2(C_171, '#skF_2', B_170) | ~v1_funct_1(C_171))), inference(negUnitSimplification, [status(thm)], [c_64, c_483])).
% 5.99/2.12  tff(c_2164, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6') | ~v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3') | ~v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_2142, c_491])).
% 5.99/2.12  tff(c_2219, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_567, c_678, c_2164])).
% 5.99/2.12  tff(c_492, plain, (![B_173, C_174]: (k3_funct_2('#skF_2', B_173, C_174, '#skF_6')=k1_funct_1(C_174, '#skF_6') | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_173))) | ~v1_funct_2(C_174, '#skF_2', B_173) | ~v1_funct_1(C_174))), inference(negUnitSimplification, [status(thm)], [c_64, c_483])).
% 5.99/2.12  tff(c_507, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_492])).
% 5.99/2.12  tff(c_513, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_507])).
% 5.99/2.12  tff(c_48, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_208])).
% 5.99/2.12  tff(c_514, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_513, c_48])).
% 5.99/2.12  tff(c_2242, plain, (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))!=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2219, c_514])).
% 5.99/2.12  tff(c_2706, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~r2_hidden('#skF_6', '#skF_2') | ~r2_hidden('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2700, c_2242])).
% 5.99/2.12  tff(c_2712, plain, (~r2_hidden('#skF_6', '#skF_2')), inference(splitLeft, [status(thm)], [c_2706])).
% 5.99/2.12  tff(c_2740, plain, (v1_xboole_0('#skF_2') | ~m1_subset_1('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_4, c_2712])).
% 5.99/2.12  tff(c_2743, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2740])).
% 5.99/2.12  tff(c_2745, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_2743])).
% 5.99/2.12  tff(c_2747, plain, (r2_hidden('#skF_6', '#skF_2')), inference(splitRight, [status(thm)], [c_2706])).
% 5.99/2.12  tff(c_2746, plain, (~r2_hidden('#skF_6', '#skF_2') | k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(splitRight, [status(thm)], [c_2706])).
% 5.99/2.12  tff(c_2749, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2747, c_2746])).
% 5.99/2.12  tff(c_2752, plain, (~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1754, c_2749])).
% 5.99/2.12  tff(c_2756, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_2752])).
% 5.99/2.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.99/2.12  
% 5.99/2.12  Inference rules
% 5.99/2.12  ----------------------
% 5.99/2.12  #Ref     : 0
% 5.99/2.12  #Sup     : 574
% 5.99/2.12  #Fact    : 0
% 5.99/2.12  #Define  : 0
% 5.99/2.12  #Split   : 23
% 5.99/2.12  #Chain   : 0
% 5.99/2.12  #Close   : 0
% 5.99/2.12  
% 5.99/2.12  Ordering : KBO
% 5.99/2.12  
% 5.99/2.12  Simplification rules
% 5.99/2.12  ----------------------
% 5.99/2.12  #Subsume      : 212
% 5.99/2.12  #Demod        : 296
% 5.99/2.12  #Tautology    : 74
% 5.99/2.12  #SimpNegUnit  : 57
% 5.99/2.12  #BackRed      : 15
% 5.99/2.12  
% 5.99/2.12  #Partial instantiations: 0
% 5.99/2.12  #Strategies tried      : 1
% 5.99/2.12  
% 5.99/2.12  Timing (in seconds)
% 5.99/2.12  ----------------------
% 5.99/2.12  Preprocessing        : 0.39
% 5.99/2.13  Parsing              : 0.20
% 5.99/2.13  CNF conversion       : 0.04
% 5.99/2.13  Main loop            : 0.93
% 5.99/2.13  Inferencing          : 0.30
% 5.99/2.13  Reduction            : 0.33
% 5.99/2.13  Demodulation         : 0.23
% 5.99/2.13  BG Simplification    : 0.04
% 5.99/2.13  Subsumption          : 0.18
% 5.99/2.13  Abstraction          : 0.05
% 5.99/2.13  MUC search           : 0.00
% 5.99/2.13  Cooper               : 0.00
% 5.99/2.13  Total                : 1.39
% 5.99/2.13  Index Insertion      : 0.00
% 5.99/2.13  Index Deletion       : 0.00
% 5.99/2.13  Index Matching       : 0.00
% 5.99/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
