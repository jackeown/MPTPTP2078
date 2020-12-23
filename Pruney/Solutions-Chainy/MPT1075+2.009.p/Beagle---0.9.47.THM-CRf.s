%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:11 EST 2020

% Result     : Theorem 4.09s
% Output     : CNFRefutation 4.37s
% Verified   : 
% Statistics : Number of formulae       :  200 ( 739 expanded)
%              Number of leaves         :   43 ( 281 expanded)
%              Depth                    :   15
%              Number of atoms          :  574 (3380 expanded)
%              Number of equality atoms :  113 ( 460 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_155,negated_conjecture,(
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
                         => k3_funct_2(B,C,k8_funct_2(B,A,C,D,E),F) = k1_funct_1(E,k3_funct_2(B,A,D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_funct_2)).

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_128,axiom,(
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

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_53,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C,D,E] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
     => ( v1_funct_1(k8_funct_2(A,B,C,D,E))
        & v1_funct_2(k8_funct_2(A,B,C,D,E),A,C)
        & m1_subset_1(k8_funct_2(A,B,C,D,E),k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_funct_2)).

tff(f_104,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(c_42,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_12,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_65,plain,(
    ! [B_86,A_87] :
      ( v1_relat_1(B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_87))
      | ~ v1_relat_1(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_71,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_48,c_65])).

tff(c_77,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_71])).

tff(c_710,plain,(
    ! [C_220,B_221,A_222] :
      ( v5_relat_1(C_220,B_221)
      | ~ m1_subset_1(C_220,k1_zfmisc_1(k2_zfmisc_1(A_222,B_221))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_718,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_710])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v5_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_50,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_742,plain,(
    ! [A_228,B_229,C_230] :
      ( k2_relset_1(A_228,B_229,C_230) = k2_relat_1(C_230)
      | ~ m1_subset_1(C_230,k1_zfmisc_1(k2_zfmisc_1(A_228,B_229))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_750,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_742])).

tff(c_932,plain,(
    ! [C_274,F_273,A_272,D_275,E_276,B_277] :
      ( k1_funct_1(k8_funct_2(B_277,C_274,A_272,D_275,E_276),F_273) = k1_funct_1(E_276,k1_funct_1(D_275,F_273))
      | k1_xboole_0 = B_277
      | ~ r1_tarski(k2_relset_1(B_277,C_274,D_275),k1_relset_1(C_274,A_272,E_276))
      | ~ m1_subset_1(F_273,B_277)
      | ~ m1_subset_1(E_276,k1_zfmisc_1(k2_zfmisc_1(C_274,A_272)))
      | ~ v1_funct_1(E_276)
      | ~ m1_subset_1(D_275,k1_zfmisc_1(k2_zfmisc_1(B_277,C_274)))
      | ~ v1_funct_2(D_275,B_277,C_274)
      | ~ v1_funct_1(D_275)
      | v1_xboole_0(C_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_938,plain,(
    ! [A_272,E_276,F_273] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_272,'#skF_4',E_276),F_273) = k1_funct_1(E_276,k1_funct_1('#skF_4',F_273))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_272,E_276))
      | ~ m1_subset_1(F_273,'#skF_2')
      | ~ m1_subset_1(E_276,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_272)))
      | ~ v1_funct_1(E_276)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_750,c_932])).

tff(c_948,plain,(
    ! [A_272,E_276,F_273] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_272,'#skF_4',E_276),F_273) = k1_funct_1(E_276,k1_funct_1('#skF_4',F_273))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_272,E_276))
      | ~ m1_subset_1(F_273,'#skF_2')
      | ~ m1_subset_1(E_276,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_272)))
      | ~ v1_funct_1(E_276)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_938])).

tff(c_949,plain,(
    ! [A_272,E_276,F_273] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_272,'#skF_4',E_276),F_273) = k1_funct_1(E_276,k1_funct_1('#skF_4',F_273))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_272,E_276))
      | ~ m1_subset_1(F_273,'#skF_2')
      | ~ m1_subset_1(E_276,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_272)))
      | ~ v1_funct_1(E_276) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_948])).

tff(c_984,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_949])).

tff(c_104,plain,(
    ! [C_98,B_99,A_100] :
      ( v5_relat_1(C_98,B_99)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_100,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_112,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_104])).

tff(c_137,plain,(
    ! [A_104,B_105,C_106] :
      ( k2_relset_1(A_104,B_105,C_106) = k2_relat_1(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_145,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_137])).

tff(c_290,plain,(
    ! [C_143,A_141,D_144,F_142,E_145,B_146] :
      ( k1_funct_1(k8_funct_2(B_146,C_143,A_141,D_144,E_145),F_142) = k1_funct_1(E_145,k1_funct_1(D_144,F_142))
      | k1_xboole_0 = B_146
      | ~ r1_tarski(k2_relset_1(B_146,C_143,D_144),k1_relset_1(C_143,A_141,E_145))
      | ~ m1_subset_1(F_142,B_146)
      | ~ m1_subset_1(E_145,k1_zfmisc_1(k2_zfmisc_1(C_143,A_141)))
      | ~ v1_funct_1(E_145)
      | ~ m1_subset_1(D_144,k1_zfmisc_1(k2_zfmisc_1(B_146,C_143)))
      | ~ v1_funct_2(D_144,B_146,C_143)
      | ~ v1_funct_1(D_144)
      | v1_xboole_0(C_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_294,plain,(
    ! [A_141,E_145,F_142] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_141,'#skF_4',E_145),F_142) = k1_funct_1(E_145,k1_funct_1('#skF_4',F_142))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_141,E_145))
      | ~ m1_subset_1(F_142,'#skF_2')
      | ~ m1_subset_1(E_145,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_141)))
      | ~ v1_funct_1(E_145)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_290])).

tff(c_303,plain,(
    ! [A_141,E_145,F_142] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_141,'#skF_4',E_145),F_142) = k1_funct_1(E_145,k1_funct_1('#skF_4',F_142))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_141,E_145))
      | ~ m1_subset_1(F_142,'#skF_2')
      | ~ m1_subset_1(E_145,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_141)))
      | ~ v1_funct_1(E_145)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_294])).

tff(c_304,plain,(
    ! [A_141,E_145,F_142] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_141,'#skF_4',E_145),F_142) = k1_funct_1(E_145,k1_funct_1('#skF_4',F_142))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_141,E_145))
      | ~ m1_subset_1(F_142,'#skF_2')
      | ~ m1_subset_1(E_145,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_141)))
      | ~ v1_funct_1(E_145) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_303])).

tff(c_336,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_304])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_60,plain,(
    ! [A_84,B_85] :
      ( r2_hidden(A_84,B_85)
      | v1_xboole_0(B_85)
      | ~ m1_subset_1(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( ~ r1_tarski(B_12,A_11)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_79,plain,(
    ! [B_90,A_91] :
      ( ~ r1_tarski(B_90,A_91)
      | v1_xboole_0(B_90)
      | ~ m1_subset_1(A_91,B_90) ) ),
    inference(resolution,[status(thm)],[c_60,c_14])).

tff(c_83,plain,(
    ! [A_1] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1(A_1,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2,c_79])).

tff(c_84,plain,(
    ! [A_1] : ~ m1_subset_1(A_1,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_338,plain,(
    ! [A_1] : ~ m1_subset_1(A_1,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_84])).

tff(c_352,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_338,c_42])).

tff(c_354,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_304])).

tff(c_46,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_68,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_65])).

tff(c_74,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_68])).

tff(c_40,plain,(
    v1_partfun1('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_95,plain,(
    ! [C_95,A_96,B_97] :
      ( v4_relat_1(C_95,A_96)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_102,plain,(
    v4_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_95])).

tff(c_114,plain,(
    ! [B_102,A_103] :
      ( k1_relat_1(B_102) = A_103
      | ~ v1_partfun1(B_102,A_103)
      | ~ v4_relat_1(B_102,A_103)
      | ~ v1_relat_1(B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_120,plain,
    ( k1_relat_1('#skF_5') = '#skF_1'
    | ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_102,c_114])).

tff(c_126,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_40,c_120])).

tff(c_150,plain,(
    ! [A_107,B_108,C_109] :
      ( k1_relset_1(A_107,B_108,C_109) = k1_relat_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_153,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_150])).

tff(c_158,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_153])).

tff(c_296,plain,(
    ! [B_146,D_144,F_142] :
      ( k1_funct_1(k8_funct_2(B_146,'#skF_1','#skF_3',D_144,'#skF_5'),F_142) = k1_funct_1('#skF_5',k1_funct_1(D_144,F_142))
      | k1_xboole_0 = B_146
      | ~ r1_tarski(k2_relset_1(B_146,'#skF_1',D_144),'#skF_1')
      | ~ m1_subset_1(F_142,B_146)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_144,k1_zfmisc_1(k2_zfmisc_1(B_146,'#skF_1')))
      | ~ v1_funct_2(D_144,B_146,'#skF_1')
      | ~ v1_funct_1(D_144)
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_290])).

tff(c_306,plain,(
    ! [B_146,D_144,F_142] :
      ( k1_funct_1(k8_funct_2(B_146,'#skF_1','#skF_3',D_144,'#skF_5'),F_142) = k1_funct_1('#skF_5',k1_funct_1(D_144,F_142))
      | k1_xboole_0 = B_146
      | ~ r1_tarski(k2_relset_1(B_146,'#skF_1',D_144),'#skF_1')
      | ~ m1_subset_1(F_142,B_146)
      | ~ m1_subset_1(D_144,k1_zfmisc_1(k2_zfmisc_1(B_146,'#skF_1')))
      | ~ v1_funct_2(D_144,B_146,'#skF_1')
      | ~ v1_funct_1(D_144)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_296])).

tff(c_454,plain,(
    ! [B_182,D_183,F_184] :
      ( k1_funct_1(k8_funct_2(B_182,'#skF_1','#skF_3',D_183,'#skF_5'),F_184) = k1_funct_1('#skF_5',k1_funct_1(D_183,F_184))
      | k1_xboole_0 = B_182
      | ~ r1_tarski(k2_relset_1(B_182,'#skF_1',D_183),'#skF_1')
      | ~ m1_subset_1(F_184,B_182)
      | ~ m1_subset_1(D_183,k1_zfmisc_1(k2_zfmisc_1(B_182,'#skF_1')))
      | ~ v1_funct_2(D_183,B_182,'#skF_1')
      | ~ v1_funct_1(D_183) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_306])).

tff(c_459,plain,(
    ! [F_184] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_184) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_184))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relset_1('#skF_2','#skF_1','#skF_4'),'#skF_1')
      | ~ m1_subset_1(F_184,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_48,c_454])).

tff(c_463,plain,(
    ! [F_184] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_184) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_184))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1')
      | ~ m1_subset_1(F_184,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_145,c_459])).

tff(c_464,plain,(
    ! [F_184] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_184) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_184))
      | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1')
      | ~ m1_subset_1(F_184,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_354,c_463])).

tff(c_474,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_464])).

tff(c_477,plain,
    ( ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_474])).

tff(c_481,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_112,c_477])).

tff(c_482,plain,(
    ! [F_184] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_184) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_184))
      | ~ m1_subset_1(F_184,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_464])).

tff(c_197,plain,(
    ! [D_122,A_121,B_119,E_120,C_118] :
      ( v1_funct_1(k8_funct_2(A_121,B_119,C_118,D_122,E_120))
      | ~ m1_subset_1(E_120,k1_zfmisc_1(k2_zfmisc_1(B_119,C_118)))
      | ~ v1_funct_1(E_120)
      | ~ m1_subset_1(D_122,k1_zfmisc_1(k2_zfmisc_1(A_121,B_119)))
      | ~ v1_funct_2(D_122,A_121,B_119)
      | ~ v1_funct_1(D_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_199,plain,(
    ! [A_121,D_122] :
      ( v1_funct_1(k8_funct_2(A_121,'#skF_1','#skF_3',D_122,'#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_122,k1_zfmisc_1(k2_zfmisc_1(A_121,'#skF_1')))
      | ~ v1_funct_2(D_122,A_121,'#skF_1')
      | ~ v1_funct_1(D_122) ) ),
    inference(resolution,[status(thm)],[c_44,c_197])).

tff(c_219,plain,(
    ! [A_128,D_129] :
      ( v1_funct_1(k8_funct_2(A_128,'#skF_1','#skF_3',D_129,'#skF_5'))
      | ~ m1_subset_1(D_129,k1_zfmisc_1(k2_zfmisc_1(A_128,'#skF_1')))
      | ~ v1_funct_2(D_129,A_128,'#skF_1')
      | ~ v1_funct_1(D_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_199])).

tff(c_222,plain,
    ( v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_219])).

tff(c_225,plain,(
    v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_222])).

tff(c_208,plain,(
    ! [D_127,E_125,A_126,B_124,C_123] :
      ( v1_funct_2(k8_funct_2(A_126,B_124,C_123,D_127,E_125),A_126,C_123)
      | ~ m1_subset_1(E_125,k1_zfmisc_1(k2_zfmisc_1(B_124,C_123)))
      | ~ v1_funct_1(E_125)
      | ~ m1_subset_1(D_127,k1_zfmisc_1(k2_zfmisc_1(A_126,B_124)))
      | ~ v1_funct_2(D_127,A_126,B_124)
      | ~ v1_funct_1(D_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_210,plain,(
    ! [A_126,D_127] :
      ( v1_funct_2(k8_funct_2(A_126,'#skF_1','#skF_3',D_127,'#skF_5'),A_126,'#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_127,k1_zfmisc_1(k2_zfmisc_1(A_126,'#skF_1')))
      | ~ v1_funct_2(D_127,A_126,'#skF_1')
      | ~ v1_funct_1(D_127) ) ),
    inference(resolution,[status(thm)],[c_44,c_208])).

tff(c_228,plain,(
    ! [A_132,D_133] :
      ( v1_funct_2(k8_funct_2(A_132,'#skF_1','#skF_3',D_133,'#skF_5'),A_132,'#skF_3')
      | ~ m1_subset_1(D_133,k1_zfmisc_1(k2_zfmisc_1(A_132,'#skF_1')))
      | ~ v1_funct_2(D_133,A_132,'#skF_1')
      | ~ v1_funct_1(D_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_210])).

tff(c_230,plain,
    ( v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_228])).

tff(c_233,plain,(
    v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_230])).

tff(c_28,plain,(
    ! [A_24,B_25,D_27,C_26,E_28] :
      ( m1_subset_1(k8_funct_2(A_24,B_25,C_26,D_27,E_28),k1_zfmisc_1(k2_zfmisc_1(A_24,C_26)))
      | ~ m1_subset_1(E_28,k1_zfmisc_1(k2_zfmisc_1(B_25,C_26)))
      | ~ v1_funct_1(E_28)
      | ~ m1_subset_1(D_27,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25)))
      | ~ v1_funct_2(D_27,A_24,B_25)
      | ~ v1_funct_1(D_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_235,plain,(
    ! [E_138,B_137,C_136,A_139,D_140] :
      ( m1_subset_1(k8_funct_2(A_139,B_137,C_136,D_140,E_138),k1_zfmisc_1(k2_zfmisc_1(A_139,C_136)))
      | ~ m1_subset_1(E_138,k1_zfmisc_1(k2_zfmisc_1(B_137,C_136)))
      | ~ v1_funct_1(E_138)
      | ~ m1_subset_1(D_140,k1_zfmisc_1(k2_zfmisc_1(A_139,B_137)))
      | ~ v1_funct_2(D_140,A_139,B_137)
      | ~ v1_funct_1(D_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_20,plain,(
    ! [A_16,B_17,C_18] :
      ( k1_relset_1(A_16,B_17,C_18) = k1_relat_1(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_424,plain,(
    ! [C_177,E_174,D_175,A_173,B_176] :
      ( k1_relset_1(A_173,C_177,k8_funct_2(A_173,B_176,C_177,D_175,E_174)) = k1_relat_1(k8_funct_2(A_173,B_176,C_177,D_175,E_174))
      | ~ m1_subset_1(E_174,k1_zfmisc_1(k2_zfmisc_1(B_176,C_177)))
      | ~ v1_funct_1(E_174)
      | ~ m1_subset_1(D_175,k1_zfmisc_1(k2_zfmisc_1(A_173,B_176)))
      | ~ v1_funct_2(D_175,A_173,B_176)
      | ~ v1_funct_1(D_175) ) ),
    inference(resolution,[status(thm)],[c_235,c_20])).

tff(c_428,plain,(
    ! [A_173,D_175] :
      ( k1_relset_1(A_173,'#skF_3',k8_funct_2(A_173,'#skF_1','#skF_3',D_175,'#skF_5')) = k1_relat_1(k8_funct_2(A_173,'#skF_1','#skF_3',D_175,'#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_175,k1_zfmisc_1(k2_zfmisc_1(A_173,'#skF_1')))
      | ~ v1_funct_2(D_175,A_173,'#skF_1')
      | ~ v1_funct_1(D_175) ) ),
    inference(resolution,[status(thm)],[c_44,c_424])).

tff(c_444,plain,(
    ! [A_180,D_181] :
      ( k1_relset_1(A_180,'#skF_3',k8_funct_2(A_180,'#skF_1','#skF_3',D_181,'#skF_5')) = k1_relat_1(k8_funct_2(A_180,'#skF_1','#skF_3',D_181,'#skF_5'))
      | ~ m1_subset_1(D_181,k1_zfmisc_1(k2_zfmisc_1(A_180,'#skF_1')))
      | ~ v1_funct_2(D_181,A_180,'#skF_1')
      | ~ v1_funct_1(D_181) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_428])).

tff(c_449,plain,
    ( k1_relset_1('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) = k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_444])).

tff(c_453,plain,(
    k1_relset_1('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) = k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_449])).

tff(c_36,plain,(
    ! [F_49,E_47,A_33,B_34,D_43,C_35] :
      ( k1_funct_1(k8_funct_2(B_34,C_35,A_33,D_43,E_47),F_49) = k1_funct_1(E_47,k1_funct_1(D_43,F_49))
      | k1_xboole_0 = B_34
      | ~ r1_tarski(k2_relset_1(B_34,C_35,D_43),k1_relset_1(C_35,A_33,E_47))
      | ~ m1_subset_1(F_49,B_34)
      | ~ m1_subset_1(E_47,k1_zfmisc_1(k2_zfmisc_1(C_35,A_33)))
      | ~ v1_funct_1(E_47)
      | ~ m1_subset_1(D_43,k1_zfmisc_1(k2_zfmisc_1(B_34,C_35)))
      | ~ v1_funct_2(D_43,B_34,C_35)
      | ~ v1_funct_1(D_43)
      | v1_xboole_0(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_467,plain,(
    ! [B_34,D_43,F_49] :
      ( k1_funct_1(k8_funct_2(B_34,'#skF_2','#skF_3',D_43,k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')),F_49) = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_funct_1(D_43,F_49))
      | k1_xboole_0 = B_34
      | ~ r1_tarski(k2_relset_1(B_34,'#skF_2',D_43),k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')))
      | ~ m1_subset_1(F_49,B_34)
      | ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_43,k1_zfmisc_1(k2_zfmisc_1(B_34,'#skF_2')))
      | ~ v1_funct_2(D_43,B_34,'#skF_2')
      | ~ v1_funct_1(D_43)
      | v1_xboole_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_453,c_36])).

tff(c_471,plain,(
    ! [B_34,D_43,F_49] :
      ( k1_funct_1(k8_funct_2(B_34,'#skF_2','#skF_3',D_43,k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')),F_49) = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_funct_1(D_43,F_49))
      | k1_xboole_0 = B_34
      | ~ r1_tarski(k2_relset_1(B_34,'#skF_2',D_43),k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')))
      | ~ m1_subset_1(F_49,B_34)
      | ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ m1_subset_1(D_43,k1_zfmisc_1(k2_zfmisc_1(B_34,'#skF_2')))
      | ~ v1_funct_2(D_43,B_34,'#skF_2')
      | ~ v1_funct_1(D_43)
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_467])).

tff(c_472,plain,(
    ! [B_34,D_43,F_49] :
      ( k1_funct_1(k8_funct_2(B_34,'#skF_2','#skF_3',D_43,k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')),F_49) = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_funct_1(D_43,F_49))
      | k1_xboole_0 = B_34
      | ~ r1_tarski(k2_relset_1(B_34,'#skF_2',D_43),k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')))
      | ~ m1_subset_1(F_49,B_34)
      | ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ m1_subset_1(D_43,k1_zfmisc_1(k2_zfmisc_1(B_34,'#skF_2')))
      | ~ v1_funct_2(D_43,B_34,'#skF_2')
      | ~ v1_funct_1(D_43) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_471])).

tff(c_598,plain,(
    ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_472])).

tff(c_601,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_598])).

tff(c_605,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_601])).

tff(c_607,plain,(
    m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_472])).

tff(c_172,plain,(
    ! [A_110,B_111,C_112,D_113] :
      ( k3_funct_2(A_110,B_111,C_112,D_113) = k1_funct_1(C_112,D_113)
      | ~ m1_subset_1(D_113,A_110)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111)))
      | ~ v1_funct_2(C_112,A_110,B_111)
      | ~ v1_funct_1(C_112)
      | v1_xboole_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_178,plain,(
    ! [B_111,C_112] :
      ( k3_funct_2('#skF_2',B_111,C_112,'#skF_6') = k1_funct_1(C_112,'#skF_6')
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_111)))
      | ~ v1_funct_2(C_112,'#skF_2',B_111)
      | ~ v1_funct_1(C_112)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_172])).

tff(c_183,plain,(
    ! [B_111,C_112] :
      ( k3_funct_2('#skF_2',B_111,C_112,'#skF_6') = k1_funct_1(C_112,'#skF_6')
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_111)))
      | ~ v1_funct_2(C_112,'#skF_2',B_111)
      | ~ v1_funct_1(C_112) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_178])).

tff(c_628,plain,
    ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6')
    | ~ v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3')
    | ~ v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_607,c_183])).

tff(c_675,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_233,c_628])).

tff(c_185,plain,(
    ! [B_116,C_117] :
      ( k3_funct_2('#skF_2',B_116,C_117,'#skF_6') = k1_funct_1(C_117,'#skF_6')
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_116)))
      | ~ v1_funct_2(C_117,'#skF_2',B_116)
      | ~ v1_funct_1(C_117) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_178])).

tff(c_188,plain,
    ( k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_185])).

tff(c_191,plain,(
    k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_188])).

tff(c_38,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_192,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_38])).

tff(c_688,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_675,c_192])).

tff(c_695,plain,(
    ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_482,c_688])).

tff(c_699,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_695])).

tff(c_700,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_986,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_984,c_700])).

tff(c_989,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_986])).

tff(c_991,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_949])).

tff(c_701,plain,(
    ! [C_217,A_218,B_219] :
      ( v4_relat_1(C_217,A_218)
      | ~ m1_subset_1(C_217,k1_zfmisc_1(k2_zfmisc_1(A_218,B_219))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_708,plain,(
    v4_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_701])).

tff(c_729,plain,(
    ! [B_226,A_227] :
      ( k1_relat_1(B_226) = A_227
      | ~ v1_partfun1(B_226,A_227)
      | ~ v4_relat_1(B_226,A_227)
      | ~ v1_relat_1(B_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_735,plain,
    ( k1_relat_1('#skF_5') = '#skF_1'
    | ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_708,c_729])).

tff(c_741,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_40,c_735])).

tff(c_769,plain,(
    ! [A_231,B_232,C_233] :
      ( k1_relset_1(A_231,B_232,C_233) = k1_relat_1(C_233)
      | ~ m1_subset_1(C_233,k1_zfmisc_1(k2_zfmisc_1(A_231,B_232))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_772,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_769])).

tff(c_777,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_741,c_772])).

tff(c_936,plain,(
    ! [B_277,D_275,F_273] :
      ( k1_funct_1(k8_funct_2(B_277,'#skF_1','#skF_3',D_275,'#skF_5'),F_273) = k1_funct_1('#skF_5',k1_funct_1(D_275,F_273))
      | k1_xboole_0 = B_277
      | ~ r1_tarski(k2_relset_1(B_277,'#skF_1',D_275),'#skF_1')
      | ~ m1_subset_1(F_273,B_277)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_275,k1_zfmisc_1(k2_zfmisc_1(B_277,'#skF_1')))
      | ~ v1_funct_2(D_275,B_277,'#skF_1')
      | ~ v1_funct_1(D_275)
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_777,c_932])).

tff(c_945,plain,(
    ! [B_277,D_275,F_273] :
      ( k1_funct_1(k8_funct_2(B_277,'#skF_1','#skF_3',D_275,'#skF_5'),F_273) = k1_funct_1('#skF_5',k1_funct_1(D_275,F_273))
      | k1_xboole_0 = B_277
      | ~ r1_tarski(k2_relset_1(B_277,'#skF_1',D_275),'#skF_1')
      | ~ m1_subset_1(F_273,B_277)
      | ~ m1_subset_1(D_275,k1_zfmisc_1(k2_zfmisc_1(B_277,'#skF_1')))
      | ~ v1_funct_2(D_275,B_277,'#skF_1')
      | ~ v1_funct_1(D_275)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_936])).

tff(c_1043,plain,(
    ! [B_301,D_302,F_303] :
      ( k1_funct_1(k8_funct_2(B_301,'#skF_1','#skF_3',D_302,'#skF_5'),F_303) = k1_funct_1('#skF_5',k1_funct_1(D_302,F_303))
      | k1_xboole_0 = B_301
      | ~ r1_tarski(k2_relset_1(B_301,'#skF_1',D_302),'#skF_1')
      | ~ m1_subset_1(F_303,B_301)
      | ~ m1_subset_1(D_302,k1_zfmisc_1(k2_zfmisc_1(B_301,'#skF_1')))
      | ~ v1_funct_2(D_302,B_301,'#skF_1')
      | ~ v1_funct_1(D_302) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_945])).

tff(c_1048,plain,(
    ! [F_303] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_303) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_303))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relset_1('#skF_2','#skF_1','#skF_4'),'#skF_1')
      | ~ m1_subset_1(F_303,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_48,c_1043])).

tff(c_1052,plain,(
    ! [F_303] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_303) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_303))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1')
      | ~ m1_subset_1(F_303,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_750,c_1048])).

tff(c_1053,plain,(
    ! [F_303] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_303) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_303))
      | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1')
      | ~ m1_subset_1(F_303,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_991,c_1052])).

tff(c_1059,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1053])).

tff(c_1062,plain,
    ( ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_1059])).

tff(c_1066,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_718,c_1062])).

tff(c_1067,plain,(
    ! [F_303] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_303) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_303))
      | ~ m1_subset_1(F_303,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_1053])).

tff(c_813,plain,(
    ! [E_244,B_243,A_245,C_242,D_246] :
      ( v1_funct_1(k8_funct_2(A_245,B_243,C_242,D_246,E_244))
      | ~ m1_subset_1(E_244,k1_zfmisc_1(k2_zfmisc_1(B_243,C_242)))
      | ~ v1_funct_1(E_244)
      | ~ m1_subset_1(D_246,k1_zfmisc_1(k2_zfmisc_1(A_245,B_243)))
      | ~ v1_funct_2(D_246,A_245,B_243)
      | ~ v1_funct_1(D_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_815,plain,(
    ! [A_245,D_246] :
      ( v1_funct_1(k8_funct_2(A_245,'#skF_1','#skF_3',D_246,'#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_246,k1_zfmisc_1(k2_zfmisc_1(A_245,'#skF_1')))
      | ~ v1_funct_2(D_246,A_245,'#skF_1')
      | ~ v1_funct_1(D_246) ) ),
    inference(resolution,[status(thm)],[c_44,c_813])).

tff(c_824,plain,(
    ! [A_247,D_248] :
      ( v1_funct_1(k8_funct_2(A_247,'#skF_1','#skF_3',D_248,'#skF_5'))
      | ~ m1_subset_1(D_248,k1_zfmisc_1(k2_zfmisc_1(A_247,'#skF_1')))
      | ~ v1_funct_2(D_248,A_247,'#skF_1')
      | ~ v1_funct_1(D_248) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_815])).

tff(c_827,plain,
    ( v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_824])).

tff(c_830,plain,(
    v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_827])).

tff(c_832,plain,(
    ! [B_252,A_254,E_253,D_255,C_251] :
      ( v1_funct_2(k8_funct_2(A_254,B_252,C_251,D_255,E_253),A_254,C_251)
      | ~ m1_subset_1(E_253,k1_zfmisc_1(k2_zfmisc_1(B_252,C_251)))
      | ~ v1_funct_1(E_253)
      | ~ m1_subset_1(D_255,k1_zfmisc_1(k2_zfmisc_1(A_254,B_252)))
      | ~ v1_funct_2(D_255,A_254,B_252)
      | ~ v1_funct_1(D_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_834,plain,(
    ! [A_254,D_255] :
      ( v1_funct_2(k8_funct_2(A_254,'#skF_1','#skF_3',D_255,'#skF_5'),A_254,'#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_255,k1_zfmisc_1(k2_zfmisc_1(A_254,'#skF_1')))
      | ~ v1_funct_2(D_255,A_254,'#skF_1')
      | ~ v1_funct_1(D_255) ) ),
    inference(resolution,[status(thm)],[c_44,c_832])).

tff(c_843,plain,(
    ! [A_256,D_257] :
      ( v1_funct_2(k8_funct_2(A_256,'#skF_1','#skF_3',D_257,'#skF_5'),A_256,'#skF_3')
      | ~ m1_subset_1(D_257,k1_zfmisc_1(k2_zfmisc_1(A_256,'#skF_1')))
      | ~ v1_funct_2(D_257,A_256,'#skF_1')
      | ~ v1_funct_1(D_257) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_834])).

tff(c_845,plain,
    ( v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_843])).

tff(c_848,plain,(
    v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_845])).

tff(c_851,plain,(
    ! [B_261,A_263,D_264,E_262,C_260] :
      ( m1_subset_1(k8_funct_2(A_263,B_261,C_260,D_264,E_262),k1_zfmisc_1(k2_zfmisc_1(A_263,C_260)))
      | ~ m1_subset_1(E_262,k1_zfmisc_1(k2_zfmisc_1(B_261,C_260)))
      | ~ v1_funct_1(E_262)
      | ~ m1_subset_1(D_264,k1_zfmisc_1(k2_zfmisc_1(A_263,B_261)))
      | ~ v1_funct_2(D_264,A_263,B_261)
      | ~ v1_funct_1(D_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1012,plain,(
    ! [D_296,A_294,B_297,E_298,C_295] :
      ( k1_relset_1(A_294,C_295,k8_funct_2(A_294,B_297,C_295,D_296,E_298)) = k1_relat_1(k8_funct_2(A_294,B_297,C_295,D_296,E_298))
      | ~ m1_subset_1(E_298,k1_zfmisc_1(k2_zfmisc_1(B_297,C_295)))
      | ~ v1_funct_1(E_298)
      | ~ m1_subset_1(D_296,k1_zfmisc_1(k2_zfmisc_1(A_294,B_297)))
      | ~ v1_funct_2(D_296,A_294,B_297)
      | ~ v1_funct_1(D_296) ) ),
    inference(resolution,[status(thm)],[c_851,c_20])).

tff(c_1016,plain,(
    ! [A_294,D_296] :
      ( k1_relset_1(A_294,'#skF_3',k8_funct_2(A_294,'#skF_1','#skF_3',D_296,'#skF_5')) = k1_relat_1(k8_funct_2(A_294,'#skF_1','#skF_3',D_296,'#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_296,k1_zfmisc_1(k2_zfmisc_1(A_294,'#skF_1')))
      | ~ v1_funct_2(D_296,A_294,'#skF_1')
      | ~ v1_funct_1(D_296) ) ),
    inference(resolution,[status(thm)],[c_44,c_1012])).

tff(c_1133,plain,(
    ! [A_321,D_322] :
      ( k1_relset_1(A_321,'#skF_3',k8_funct_2(A_321,'#skF_1','#skF_3',D_322,'#skF_5')) = k1_relat_1(k8_funct_2(A_321,'#skF_1','#skF_3',D_322,'#skF_5'))
      | ~ m1_subset_1(D_322,k1_zfmisc_1(k2_zfmisc_1(A_321,'#skF_1')))
      | ~ v1_funct_2(D_322,A_321,'#skF_1')
      | ~ v1_funct_1(D_322) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1016])).

tff(c_1138,plain,
    ( k1_relset_1('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) = k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_1133])).

tff(c_1142,plain,(
    k1_relset_1('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) = k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1138])).

tff(c_1159,plain,(
    ! [B_34,D_43,F_49] :
      ( k1_funct_1(k8_funct_2(B_34,'#skF_2','#skF_3',D_43,k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')),F_49) = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_funct_1(D_43,F_49))
      | k1_xboole_0 = B_34
      | ~ r1_tarski(k2_relset_1(B_34,'#skF_2',D_43),k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')))
      | ~ m1_subset_1(F_49,B_34)
      | ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_43,k1_zfmisc_1(k2_zfmisc_1(B_34,'#skF_2')))
      | ~ v1_funct_2(D_43,B_34,'#skF_2')
      | ~ v1_funct_1(D_43)
      | v1_xboole_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1142,c_36])).

tff(c_1163,plain,(
    ! [B_34,D_43,F_49] :
      ( k1_funct_1(k8_funct_2(B_34,'#skF_2','#skF_3',D_43,k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')),F_49) = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_funct_1(D_43,F_49))
      | k1_xboole_0 = B_34
      | ~ r1_tarski(k2_relset_1(B_34,'#skF_2',D_43),k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')))
      | ~ m1_subset_1(F_49,B_34)
      | ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ m1_subset_1(D_43,k1_zfmisc_1(k2_zfmisc_1(B_34,'#skF_2')))
      | ~ v1_funct_2(D_43,B_34,'#skF_2')
      | ~ v1_funct_1(D_43)
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_830,c_1159])).

tff(c_1164,plain,(
    ! [B_34,D_43,F_49] :
      ( k1_funct_1(k8_funct_2(B_34,'#skF_2','#skF_3',D_43,k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')),F_49) = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_funct_1(D_43,F_49))
      | k1_xboole_0 = B_34
      | ~ r1_tarski(k2_relset_1(B_34,'#skF_2',D_43),k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')))
      | ~ m1_subset_1(F_49,B_34)
      | ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ m1_subset_1(D_43,k1_zfmisc_1(k2_zfmisc_1(B_34,'#skF_2')))
      | ~ v1_funct_2(D_43,B_34,'#skF_2')
      | ~ v1_funct_1(D_43) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1163])).

tff(c_1187,plain,(
    ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1164])).

tff(c_1190,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_1187])).

tff(c_1194,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_1190])).

tff(c_1196,plain,(
    m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1164])).

tff(c_788,plain,(
    ! [A_236,B_237,C_238,D_239] :
      ( k3_funct_2(A_236,B_237,C_238,D_239) = k1_funct_1(C_238,D_239)
      | ~ m1_subset_1(D_239,A_236)
      | ~ m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(A_236,B_237)))
      | ~ v1_funct_2(C_238,A_236,B_237)
      | ~ v1_funct_1(C_238)
      | v1_xboole_0(A_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_794,plain,(
    ! [B_237,C_238] :
      ( k3_funct_2('#skF_2',B_237,C_238,'#skF_6') = k1_funct_1(C_238,'#skF_6')
      | ~ m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_237)))
      | ~ v1_funct_2(C_238,'#skF_2',B_237)
      | ~ v1_funct_1(C_238)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_788])).

tff(c_799,plain,(
    ! [B_237,C_238] :
      ( k3_funct_2('#skF_2',B_237,C_238,'#skF_6') = k1_funct_1(C_238,'#skF_6')
      | ~ m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_237)))
      | ~ v1_funct_2(C_238,'#skF_2',B_237)
      | ~ v1_funct_1(C_238) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_794])).

tff(c_1215,plain,
    ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6')
    | ~ v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3')
    | ~ v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_1196,c_799])).

tff(c_1259,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_830,c_848,c_1215])).

tff(c_800,plain,(
    ! [B_240,C_241] :
      ( k3_funct_2('#skF_2',B_240,C_241,'#skF_6') = k1_funct_1(C_241,'#skF_6')
      | ~ m1_subset_1(C_241,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_240)))
      | ~ v1_funct_2(C_241,'#skF_2',B_240)
      | ~ v1_funct_1(C_241) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_794])).

tff(c_803,plain,
    ( k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_800])).

tff(c_806,plain,(
    k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_803])).

tff(c_807,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_806,c_38])).

tff(c_1272,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1259,c_807])).

tff(c_1279,plain,(
    ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1067,c_1272])).

tff(c_1283,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1279])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:06:24 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.09/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.09/1.67  
% 4.09/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.09/1.68  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.09/1.68  
% 4.09/1.68  %Foreground sorts:
% 4.09/1.68  
% 4.09/1.68  
% 4.09/1.68  %Background operators:
% 4.09/1.68  
% 4.09/1.68  
% 4.09/1.68  %Foreground operators:
% 4.09/1.68  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.09/1.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.09/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.09/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.09/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.09/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.09/1.68  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.09/1.68  tff('#skF_5', type, '#skF_5': $i).
% 4.09/1.68  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.09/1.68  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 4.09/1.68  tff('#skF_6', type, '#skF_6': $i).
% 4.09/1.68  tff('#skF_2', type, '#skF_2': $i).
% 4.09/1.68  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.09/1.68  tff('#skF_3', type, '#skF_3': $i).
% 4.09/1.68  tff('#skF_1', type, '#skF_1': $i).
% 4.09/1.68  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.09/1.68  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.09/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.09/1.68  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.09/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.09/1.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.09/1.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.09/1.68  tff('#skF_4', type, '#skF_4': $i).
% 4.09/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.09/1.68  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.09/1.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.09/1.68  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 4.09/1.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.09/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.09/1.68  
% 4.37/1.71  tff(f_155, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k1_funct_1(E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_funct_2)).
% 4.37/1.71  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.37/1.71  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.37/1.71  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.37/1.71  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 4.37/1.71  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.37/1.71  tff(f_128, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 4.37/1.71  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.37/1.71  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.37/1.71  tff(f_53, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.37/1.71  tff(f_75, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 4.37/1.71  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.37/1.71  tff(f_91, axiom, (![A, B, C, D, E]: (((((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(E)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v1_funct_1(k8_funct_2(A, B, C, D, E)) & v1_funct_2(k8_funct_2(A, B, C, D, E), A, C)) & m1_subset_1(k8_funct_2(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(A, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_funct_2)).
% 4.37/1.71  tff(f_104, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 4.37/1.71  tff(c_42, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.37/1.71  tff(c_12, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.37/1.71  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.37/1.71  tff(c_65, plain, (![B_86, A_87]: (v1_relat_1(B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(A_87)) | ~v1_relat_1(A_87))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.37/1.71  tff(c_71, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_48, c_65])).
% 4.37/1.71  tff(c_77, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_71])).
% 4.37/1.71  tff(c_710, plain, (![C_220, B_221, A_222]: (v5_relat_1(C_220, B_221) | ~m1_subset_1(C_220, k1_zfmisc_1(k2_zfmisc_1(A_222, B_221))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.37/1.71  tff(c_718, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_710])).
% 4.37/1.71  tff(c_10, plain, (![B_8, A_7]: (r1_tarski(k2_relat_1(B_8), A_7) | ~v5_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.37/1.71  tff(c_54, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.37/1.71  tff(c_56, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.37/1.71  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.37/1.71  tff(c_50, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.37/1.71  tff(c_742, plain, (![A_228, B_229, C_230]: (k2_relset_1(A_228, B_229, C_230)=k2_relat_1(C_230) | ~m1_subset_1(C_230, k1_zfmisc_1(k2_zfmisc_1(A_228, B_229))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.37/1.71  tff(c_750, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_742])).
% 4.37/1.71  tff(c_932, plain, (![C_274, F_273, A_272, D_275, E_276, B_277]: (k1_funct_1(k8_funct_2(B_277, C_274, A_272, D_275, E_276), F_273)=k1_funct_1(E_276, k1_funct_1(D_275, F_273)) | k1_xboole_0=B_277 | ~r1_tarski(k2_relset_1(B_277, C_274, D_275), k1_relset_1(C_274, A_272, E_276)) | ~m1_subset_1(F_273, B_277) | ~m1_subset_1(E_276, k1_zfmisc_1(k2_zfmisc_1(C_274, A_272))) | ~v1_funct_1(E_276) | ~m1_subset_1(D_275, k1_zfmisc_1(k2_zfmisc_1(B_277, C_274))) | ~v1_funct_2(D_275, B_277, C_274) | ~v1_funct_1(D_275) | v1_xboole_0(C_274))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.37/1.71  tff(c_938, plain, (![A_272, E_276, F_273]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_272, '#skF_4', E_276), F_273)=k1_funct_1(E_276, k1_funct_1('#skF_4', F_273)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_272, E_276)) | ~m1_subset_1(F_273, '#skF_2') | ~m1_subset_1(E_276, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_272))) | ~v1_funct_1(E_276) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_750, c_932])).
% 4.37/1.71  tff(c_948, plain, (![A_272, E_276, F_273]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_272, '#skF_4', E_276), F_273)=k1_funct_1(E_276, k1_funct_1('#skF_4', F_273)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_272, E_276)) | ~m1_subset_1(F_273, '#skF_2') | ~m1_subset_1(E_276, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_272))) | ~v1_funct_1(E_276) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_938])).
% 4.37/1.71  tff(c_949, plain, (![A_272, E_276, F_273]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_272, '#skF_4', E_276), F_273)=k1_funct_1(E_276, k1_funct_1('#skF_4', F_273)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_272, E_276)) | ~m1_subset_1(F_273, '#skF_2') | ~m1_subset_1(E_276, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_272))) | ~v1_funct_1(E_276))), inference(negUnitSimplification, [status(thm)], [c_56, c_948])).
% 4.37/1.71  tff(c_984, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_949])).
% 4.37/1.71  tff(c_104, plain, (![C_98, B_99, A_100]: (v5_relat_1(C_98, B_99) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_100, B_99))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.37/1.71  tff(c_112, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_104])).
% 4.37/1.71  tff(c_137, plain, (![A_104, B_105, C_106]: (k2_relset_1(A_104, B_105, C_106)=k2_relat_1(C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.37/1.71  tff(c_145, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_137])).
% 4.37/1.71  tff(c_290, plain, (![C_143, A_141, D_144, F_142, E_145, B_146]: (k1_funct_1(k8_funct_2(B_146, C_143, A_141, D_144, E_145), F_142)=k1_funct_1(E_145, k1_funct_1(D_144, F_142)) | k1_xboole_0=B_146 | ~r1_tarski(k2_relset_1(B_146, C_143, D_144), k1_relset_1(C_143, A_141, E_145)) | ~m1_subset_1(F_142, B_146) | ~m1_subset_1(E_145, k1_zfmisc_1(k2_zfmisc_1(C_143, A_141))) | ~v1_funct_1(E_145) | ~m1_subset_1(D_144, k1_zfmisc_1(k2_zfmisc_1(B_146, C_143))) | ~v1_funct_2(D_144, B_146, C_143) | ~v1_funct_1(D_144) | v1_xboole_0(C_143))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.37/1.71  tff(c_294, plain, (![A_141, E_145, F_142]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_141, '#skF_4', E_145), F_142)=k1_funct_1(E_145, k1_funct_1('#skF_4', F_142)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_141, E_145)) | ~m1_subset_1(F_142, '#skF_2') | ~m1_subset_1(E_145, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_141))) | ~v1_funct_1(E_145) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_145, c_290])).
% 4.37/1.71  tff(c_303, plain, (![A_141, E_145, F_142]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_141, '#skF_4', E_145), F_142)=k1_funct_1(E_145, k1_funct_1('#skF_4', F_142)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_141, E_145)) | ~m1_subset_1(F_142, '#skF_2') | ~m1_subset_1(E_145, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_141))) | ~v1_funct_1(E_145) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_294])).
% 4.37/1.71  tff(c_304, plain, (![A_141, E_145, F_142]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_141, '#skF_4', E_145), F_142)=k1_funct_1(E_145, k1_funct_1('#skF_4', F_142)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_141, E_145)) | ~m1_subset_1(F_142, '#skF_2') | ~m1_subset_1(E_145, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_141))) | ~v1_funct_1(E_145))), inference(negUnitSimplification, [status(thm)], [c_56, c_303])).
% 4.37/1.71  tff(c_336, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_304])).
% 4.37/1.71  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.37/1.71  tff(c_60, plain, (![A_84, B_85]: (r2_hidden(A_84, B_85) | v1_xboole_0(B_85) | ~m1_subset_1(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.37/1.71  tff(c_14, plain, (![B_12, A_11]: (~r1_tarski(B_12, A_11) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.37/1.71  tff(c_79, plain, (![B_90, A_91]: (~r1_tarski(B_90, A_91) | v1_xboole_0(B_90) | ~m1_subset_1(A_91, B_90))), inference(resolution, [status(thm)], [c_60, c_14])).
% 4.37/1.71  tff(c_83, plain, (![A_1]: (v1_xboole_0(k1_xboole_0) | ~m1_subset_1(A_1, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_79])).
% 4.37/1.71  tff(c_84, plain, (![A_1]: (~m1_subset_1(A_1, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_83])).
% 4.37/1.71  tff(c_338, plain, (![A_1]: (~m1_subset_1(A_1, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_336, c_84])).
% 4.37/1.71  tff(c_352, plain, $false, inference(negUnitSimplification, [status(thm)], [c_338, c_42])).
% 4.37/1.71  tff(c_354, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_304])).
% 4.37/1.71  tff(c_46, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.37/1.71  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.37/1.71  tff(c_68, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_44, c_65])).
% 4.37/1.71  tff(c_74, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_68])).
% 4.37/1.71  tff(c_40, plain, (v1_partfun1('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.37/1.71  tff(c_95, plain, (![C_95, A_96, B_97]: (v4_relat_1(C_95, A_96) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.37/1.71  tff(c_102, plain, (v4_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_44, c_95])).
% 4.37/1.71  tff(c_114, plain, (![B_102, A_103]: (k1_relat_1(B_102)=A_103 | ~v1_partfun1(B_102, A_103) | ~v4_relat_1(B_102, A_103) | ~v1_relat_1(B_102))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.37/1.71  tff(c_120, plain, (k1_relat_1('#skF_5')='#skF_1' | ~v1_partfun1('#skF_5', '#skF_1') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_102, c_114])).
% 4.37/1.71  tff(c_126, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_40, c_120])).
% 4.37/1.71  tff(c_150, plain, (![A_107, B_108, C_109]: (k1_relset_1(A_107, B_108, C_109)=k1_relat_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.37/1.71  tff(c_153, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_150])).
% 4.37/1.71  tff(c_158, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_126, c_153])).
% 4.37/1.71  tff(c_296, plain, (![B_146, D_144, F_142]: (k1_funct_1(k8_funct_2(B_146, '#skF_1', '#skF_3', D_144, '#skF_5'), F_142)=k1_funct_1('#skF_5', k1_funct_1(D_144, F_142)) | k1_xboole_0=B_146 | ~r1_tarski(k2_relset_1(B_146, '#skF_1', D_144), '#skF_1') | ~m1_subset_1(F_142, B_146) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_144, k1_zfmisc_1(k2_zfmisc_1(B_146, '#skF_1'))) | ~v1_funct_2(D_144, B_146, '#skF_1') | ~v1_funct_1(D_144) | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_158, c_290])).
% 4.37/1.71  tff(c_306, plain, (![B_146, D_144, F_142]: (k1_funct_1(k8_funct_2(B_146, '#skF_1', '#skF_3', D_144, '#skF_5'), F_142)=k1_funct_1('#skF_5', k1_funct_1(D_144, F_142)) | k1_xboole_0=B_146 | ~r1_tarski(k2_relset_1(B_146, '#skF_1', D_144), '#skF_1') | ~m1_subset_1(F_142, B_146) | ~m1_subset_1(D_144, k1_zfmisc_1(k2_zfmisc_1(B_146, '#skF_1'))) | ~v1_funct_2(D_144, B_146, '#skF_1') | ~v1_funct_1(D_144) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_296])).
% 4.37/1.71  tff(c_454, plain, (![B_182, D_183, F_184]: (k1_funct_1(k8_funct_2(B_182, '#skF_1', '#skF_3', D_183, '#skF_5'), F_184)=k1_funct_1('#skF_5', k1_funct_1(D_183, F_184)) | k1_xboole_0=B_182 | ~r1_tarski(k2_relset_1(B_182, '#skF_1', D_183), '#skF_1') | ~m1_subset_1(F_184, B_182) | ~m1_subset_1(D_183, k1_zfmisc_1(k2_zfmisc_1(B_182, '#skF_1'))) | ~v1_funct_2(D_183, B_182, '#skF_1') | ~v1_funct_1(D_183))), inference(negUnitSimplification, [status(thm)], [c_56, c_306])).
% 4.37/1.71  tff(c_459, plain, (![F_184]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_184)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_184)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relset_1('#skF_2', '#skF_1', '#skF_4'), '#skF_1') | ~m1_subset_1(F_184, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_48, c_454])).
% 4.37/1.71  tff(c_463, plain, (![F_184]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_184)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_184)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_1') | ~m1_subset_1(F_184, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_145, c_459])).
% 4.37/1.71  tff(c_464, plain, (![F_184]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_184)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_184)) | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_1') | ~m1_subset_1(F_184, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_354, c_463])).
% 4.37/1.71  tff(c_474, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(splitLeft, [status(thm)], [c_464])).
% 4.37/1.71  tff(c_477, plain, (~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_474])).
% 4.37/1.71  tff(c_481, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_77, c_112, c_477])).
% 4.37/1.71  tff(c_482, plain, (![F_184]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_184)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_184)) | ~m1_subset_1(F_184, '#skF_2'))), inference(splitRight, [status(thm)], [c_464])).
% 4.37/1.71  tff(c_197, plain, (![D_122, A_121, B_119, E_120, C_118]: (v1_funct_1(k8_funct_2(A_121, B_119, C_118, D_122, E_120)) | ~m1_subset_1(E_120, k1_zfmisc_1(k2_zfmisc_1(B_119, C_118))) | ~v1_funct_1(E_120) | ~m1_subset_1(D_122, k1_zfmisc_1(k2_zfmisc_1(A_121, B_119))) | ~v1_funct_2(D_122, A_121, B_119) | ~v1_funct_1(D_122))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.37/1.71  tff(c_199, plain, (![A_121, D_122]: (v1_funct_1(k8_funct_2(A_121, '#skF_1', '#skF_3', D_122, '#skF_5')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_122, k1_zfmisc_1(k2_zfmisc_1(A_121, '#skF_1'))) | ~v1_funct_2(D_122, A_121, '#skF_1') | ~v1_funct_1(D_122))), inference(resolution, [status(thm)], [c_44, c_197])).
% 4.37/1.71  tff(c_219, plain, (![A_128, D_129]: (v1_funct_1(k8_funct_2(A_128, '#skF_1', '#skF_3', D_129, '#skF_5')) | ~m1_subset_1(D_129, k1_zfmisc_1(k2_zfmisc_1(A_128, '#skF_1'))) | ~v1_funct_2(D_129, A_128, '#skF_1') | ~v1_funct_1(D_129))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_199])).
% 4.37/1.71  tff(c_222, plain, (v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_219])).
% 4.37/1.71  tff(c_225, plain, (v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_222])).
% 4.37/1.71  tff(c_208, plain, (![D_127, E_125, A_126, B_124, C_123]: (v1_funct_2(k8_funct_2(A_126, B_124, C_123, D_127, E_125), A_126, C_123) | ~m1_subset_1(E_125, k1_zfmisc_1(k2_zfmisc_1(B_124, C_123))) | ~v1_funct_1(E_125) | ~m1_subset_1(D_127, k1_zfmisc_1(k2_zfmisc_1(A_126, B_124))) | ~v1_funct_2(D_127, A_126, B_124) | ~v1_funct_1(D_127))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.37/1.71  tff(c_210, plain, (![A_126, D_127]: (v1_funct_2(k8_funct_2(A_126, '#skF_1', '#skF_3', D_127, '#skF_5'), A_126, '#skF_3') | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_127, k1_zfmisc_1(k2_zfmisc_1(A_126, '#skF_1'))) | ~v1_funct_2(D_127, A_126, '#skF_1') | ~v1_funct_1(D_127))), inference(resolution, [status(thm)], [c_44, c_208])).
% 4.37/1.71  tff(c_228, plain, (![A_132, D_133]: (v1_funct_2(k8_funct_2(A_132, '#skF_1', '#skF_3', D_133, '#skF_5'), A_132, '#skF_3') | ~m1_subset_1(D_133, k1_zfmisc_1(k2_zfmisc_1(A_132, '#skF_1'))) | ~v1_funct_2(D_133, A_132, '#skF_1') | ~v1_funct_1(D_133))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_210])).
% 4.37/1.71  tff(c_230, plain, (v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_228])).
% 4.37/1.71  tff(c_233, plain, (v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_230])).
% 4.37/1.71  tff(c_28, plain, (![A_24, B_25, D_27, C_26, E_28]: (m1_subset_1(k8_funct_2(A_24, B_25, C_26, D_27, E_28), k1_zfmisc_1(k2_zfmisc_1(A_24, C_26))) | ~m1_subset_1(E_28, k1_zfmisc_1(k2_zfmisc_1(B_25, C_26))) | ~v1_funct_1(E_28) | ~m1_subset_1(D_27, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))) | ~v1_funct_2(D_27, A_24, B_25) | ~v1_funct_1(D_27))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.37/1.71  tff(c_235, plain, (![E_138, B_137, C_136, A_139, D_140]: (m1_subset_1(k8_funct_2(A_139, B_137, C_136, D_140, E_138), k1_zfmisc_1(k2_zfmisc_1(A_139, C_136))) | ~m1_subset_1(E_138, k1_zfmisc_1(k2_zfmisc_1(B_137, C_136))) | ~v1_funct_1(E_138) | ~m1_subset_1(D_140, k1_zfmisc_1(k2_zfmisc_1(A_139, B_137))) | ~v1_funct_2(D_140, A_139, B_137) | ~v1_funct_1(D_140))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.37/1.71  tff(c_20, plain, (![A_16, B_17, C_18]: (k1_relset_1(A_16, B_17, C_18)=k1_relat_1(C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.37/1.71  tff(c_424, plain, (![C_177, E_174, D_175, A_173, B_176]: (k1_relset_1(A_173, C_177, k8_funct_2(A_173, B_176, C_177, D_175, E_174))=k1_relat_1(k8_funct_2(A_173, B_176, C_177, D_175, E_174)) | ~m1_subset_1(E_174, k1_zfmisc_1(k2_zfmisc_1(B_176, C_177))) | ~v1_funct_1(E_174) | ~m1_subset_1(D_175, k1_zfmisc_1(k2_zfmisc_1(A_173, B_176))) | ~v1_funct_2(D_175, A_173, B_176) | ~v1_funct_1(D_175))), inference(resolution, [status(thm)], [c_235, c_20])).
% 4.37/1.71  tff(c_428, plain, (![A_173, D_175]: (k1_relset_1(A_173, '#skF_3', k8_funct_2(A_173, '#skF_1', '#skF_3', D_175, '#skF_5'))=k1_relat_1(k8_funct_2(A_173, '#skF_1', '#skF_3', D_175, '#skF_5')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_175, k1_zfmisc_1(k2_zfmisc_1(A_173, '#skF_1'))) | ~v1_funct_2(D_175, A_173, '#skF_1') | ~v1_funct_1(D_175))), inference(resolution, [status(thm)], [c_44, c_424])).
% 4.37/1.71  tff(c_444, plain, (![A_180, D_181]: (k1_relset_1(A_180, '#skF_3', k8_funct_2(A_180, '#skF_1', '#skF_3', D_181, '#skF_5'))=k1_relat_1(k8_funct_2(A_180, '#skF_1', '#skF_3', D_181, '#skF_5')) | ~m1_subset_1(D_181, k1_zfmisc_1(k2_zfmisc_1(A_180, '#skF_1'))) | ~v1_funct_2(D_181, A_180, '#skF_1') | ~v1_funct_1(D_181))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_428])).
% 4.37/1.71  tff(c_449, plain, (k1_relset_1('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))=k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_444])).
% 4.37/1.71  tff(c_453, plain, (k1_relset_1('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))=k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_449])).
% 4.37/1.71  tff(c_36, plain, (![F_49, E_47, A_33, B_34, D_43, C_35]: (k1_funct_1(k8_funct_2(B_34, C_35, A_33, D_43, E_47), F_49)=k1_funct_1(E_47, k1_funct_1(D_43, F_49)) | k1_xboole_0=B_34 | ~r1_tarski(k2_relset_1(B_34, C_35, D_43), k1_relset_1(C_35, A_33, E_47)) | ~m1_subset_1(F_49, B_34) | ~m1_subset_1(E_47, k1_zfmisc_1(k2_zfmisc_1(C_35, A_33))) | ~v1_funct_1(E_47) | ~m1_subset_1(D_43, k1_zfmisc_1(k2_zfmisc_1(B_34, C_35))) | ~v1_funct_2(D_43, B_34, C_35) | ~v1_funct_1(D_43) | v1_xboole_0(C_35))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.37/1.71  tff(c_467, plain, (![B_34, D_43, F_49]: (k1_funct_1(k8_funct_2(B_34, '#skF_2', '#skF_3', D_43, k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')), F_49)=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_funct_1(D_43, F_49)) | k1_xboole_0=B_34 | ~r1_tarski(k2_relset_1(B_34, '#skF_2', D_43), k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(F_49, B_34) | ~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_43, k1_zfmisc_1(k2_zfmisc_1(B_34, '#skF_2'))) | ~v1_funct_2(D_43, B_34, '#skF_2') | ~v1_funct_1(D_43) | v1_xboole_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_453, c_36])).
% 4.37/1.71  tff(c_471, plain, (![B_34, D_43, F_49]: (k1_funct_1(k8_funct_2(B_34, '#skF_2', '#skF_3', D_43, k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')), F_49)=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_funct_1(D_43, F_49)) | k1_xboole_0=B_34 | ~r1_tarski(k2_relset_1(B_34, '#skF_2', D_43), k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(F_49, B_34) | ~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1(D_43, k1_zfmisc_1(k2_zfmisc_1(B_34, '#skF_2'))) | ~v1_funct_2(D_43, B_34, '#skF_2') | ~v1_funct_1(D_43) | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_225, c_467])).
% 4.37/1.71  tff(c_472, plain, (![B_34, D_43, F_49]: (k1_funct_1(k8_funct_2(B_34, '#skF_2', '#skF_3', D_43, k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')), F_49)=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_funct_1(D_43, F_49)) | k1_xboole_0=B_34 | ~r1_tarski(k2_relset_1(B_34, '#skF_2', D_43), k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(F_49, B_34) | ~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1(D_43, k1_zfmisc_1(k2_zfmisc_1(B_34, '#skF_2'))) | ~v1_funct_2(D_43, B_34, '#skF_2') | ~v1_funct_1(D_43))), inference(negUnitSimplification, [status(thm)], [c_54, c_471])).
% 4.37/1.71  tff(c_598, plain, (~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_472])).
% 4.37/1.71  tff(c_601, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_598])).
% 4.37/1.71  tff(c_605, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_601])).
% 4.37/1.71  tff(c_607, plain, (m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_472])).
% 4.37/1.71  tff(c_172, plain, (![A_110, B_111, C_112, D_113]: (k3_funct_2(A_110, B_111, C_112, D_113)=k1_funct_1(C_112, D_113) | ~m1_subset_1(D_113, A_110) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))) | ~v1_funct_2(C_112, A_110, B_111) | ~v1_funct_1(C_112) | v1_xboole_0(A_110))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.37/1.71  tff(c_178, plain, (![B_111, C_112]: (k3_funct_2('#skF_2', B_111, C_112, '#skF_6')=k1_funct_1(C_112, '#skF_6') | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_111))) | ~v1_funct_2(C_112, '#skF_2', B_111) | ~v1_funct_1(C_112) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_172])).
% 4.37/1.71  tff(c_183, plain, (![B_111, C_112]: (k3_funct_2('#skF_2', B_111, C_112, '#skF_6')=k1_funct_1(C_112, '#skF_6') | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_111))) | ~v1_funct_2(C_112, '#skF_2', B_111) | ~v1_funct_1(C_112))), inference(negUnitSimplification, [status(thm)], [c_54, c_178])).
% 4.37/1.71  tff(c_628, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6') | ~v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3') | ~v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_607, c_183])).
% 4.37/1.71  tff(c_675, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_225, c_233, c_628])).
% 4.37/1.71  tff(c_185, plain, (![B_116, C_117]: (k3_funct_2('#skF_2', B_116, C_117, '#skF_6')=k1_funct_1(C_117, '#skF_6') | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_116))) | ~v1_funct_2(C_117, '#skF_2', B_116) | ~v1_funct_1(C_117))), inference(negUnitSimplification, [status(thm)], [c_54, c_178])).
% 4.37/1.71  tff(c_188, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_185])).
% 4.37/1.71  tff(c_191, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_188])).
% 4.37/1.71  tff(c_38, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.37/1.71  tff(c_192, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_191, c_38])).
% 4.37/1.71  tff(c_688, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_675, c_192])).
% 4.37/1.71  tff(c_695, plain, (~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_482, c_688])).
% 4.37/1.71  tff(c_699, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_695])).
% 4.37/1.71  tff(c_700, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_83])).
% 4.37/1.71  tff(c_986, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_984, c_700])).
% 4.37/1.71  tff(c_989, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_986])).
% 4.37/1.71  tff(c_991, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_949])).
% 4.37/1.71  tff(c_701, plain, (![C_217, A_218, B_219]: (v4_relat_1(C_217, A_218) | ~m1_subset_1(C_217, k1_zfmisc_1(k2_zfmisc_1(A_218, B_219))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.37/1.71  tff(c_708, plain, (v4_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_44, c_701])).
% 4.37/1.71  tff(c_729, plain, (![B_226, A_227]: (k1_relat_1(B_226)=A_227 | ~v1_partfun1(B_226, A_227) | ~v4_relat_1(B_226, A_227) | ~v1_relat_1(B_226))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.37/1.71  tff(c_735, plain, (k1_relat_1('#skF_5')='#skF_1' | ~v1_partfun1('#skF_5', '#skF_1') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_708, c_729])).
% 4.37/1.71  tff(c_741, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_40, c_735])).
% 4.37/1.71  tff(c_769, plain, (![A_231, B_232, C_233]: (k1_relset_1(A_231, B_232, C_233)=k1_relat_1(C_233) | ~m1_subset_1(C_233, k1_zfmisc_1(k2_zfmisc_1(A_231, B_232))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.37/1.71  tff(c_772, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_769])).
% 4.37/1.71  tff(c_777, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_741, c_772])).
% 4.37/1.71  tff(c_936, plain, (![B_277, D_275, F_273]: (k1_funct_1(k8_funct_2(B_277, '#skF_1', '#skF_3', D_275, '#skF_5'), F_273)=k1_funct_1('#skF_5', k1_funct_1(D_275, F_273)) | k1_xboole_0=B_277 | ~r1_tarski(k2_relset_1(B_277, '#skF_1', D_275), '#skF_1') | ~m1_subset_1(F_273, B_277) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_275, k1_zfmisc_1(k2_zfmisc_1(B_277, '#skF_1'))) | ~v1_funct_2(D_275, B_277, '#skF_1') | ~v1_funct_1(D_275) | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_777, c_932])).
% 4.37/1.71  tff(c_945, plain, (![B_277, D_275, F_273]: (k1_funct_1(k8_funct_2(B_277, '#skF_1', '#skF_3', D_275, '#skF_5'), F_273)=k1_funct_1('#skF_5', k1_funct_1(D_275, F_273)) | k1_xboole_0=B_277 | ~r1_tarski(k2_relset_1(B_277, '#skF_1', D_275), '#skF_1') | ~m1_subset_1(F_273, B_277) | ~m1_subset_1(D_275, k1_zfmisc_1(k2_zfmisc_1(B_277, '#skF_1'))) | ~v1_funct_2(D_275, B_277, '#skF_1') | ~v1_funct_1(D_275) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_936])).
% 4.37/1.71  tff(c_1043, plain, (![B_301, D_302, F_303]: (k1_funct_1(k8_funct_2(B_301, '#skF_1', '#skF_3', D_302, '#skF_5'), F_303)=k1_funct_1('#skF_5', k1_funct_1(D_302, F_303)) | k1_xboole_0=B_301 | ~r1_tarski(k2_relset_1(B_301, '#skF_1', D_302), '#skF_1') | ~m1_subset_1(F_303, B_301) | ~m1_subset_1(D_302, k1_zfmisc_1(k2_zfmisc_1(B_301, '#skF_1'))) | ~v1_funct_2(D_302, B_301, '#skF_1') | ~v1_funct_1(D_302))), inference(negUnitSimplification, [status(thm)], [c_56, c_945])).
% 4.37/1.71  tff(c_1048, plain, (![F_303]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_303)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_303)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relset_1('#skF_2', '#skF_1', '#skF_4'), '#skF_1') | ~m1_subset_1(F_303, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_48, c_1043])).
% 4.37/1.71  tff(c_1052, plain, (![F_303]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_303)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_303)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_1') | ~m1_subset_1(F_303, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_750, c_1048])).
% 4.37/1.71  tff(c_1053, plain, (![F_303]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_303)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_303)) | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_1') | ~m1_subset_1(F_303, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_991, c_1052])).
% 4.37/1.71  tff(c_1059, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(splitLeft, [status(thm)], [c_1053])).
% 4.37/1.71  tff(c_1062, plain, (~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_1059])).
% 4.37/1.71  tff(c_1066, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_77, c_718, c_1062])).
% 4.37/1.71  tff(c_1067, plain, (![F_303]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_303)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_303)) | ~m1_subset_1(F_303, '#skF_2'))), inference(splitRight, [status(thm)], [c_1053])).
% 4.37/1.71  tff(c_813, plain, (![E_244, B_243, A_245, C_242, D_246]: (v1_funct_1(k8_funct_2(A_245, B_243, C_242, D_246, E_244)) | ~m1_subset_1(E_244, k1_zfmisc_1(k2_zfmisc_1(B_243, C_242))) | ~v1_funct_1(E_244) | ~m1_subset_1(D_246, k1_zfmisc_1(k2_zfmisc_1(A_245, B_243))) | ~v1_funct_2(D_246, A_245, B_243) | ~v1_funct_1(D_246))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.37/1.71  tff(c_815, plain, (![A_245, D_246]: (v1_funct_1(k8_funct_2(A_245, '#skF_1', '#skF_3', D_246, '#skF_5')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_246, k1_zfmisc_1(k2_zfmisc_1(A_245, '#skF_1'))) | ~v1_funct_2(D_246, A_245, '#skF_1') | ~v1_funct_1(D_246))), inference(resolution, [status(thm)], [c_44, c_813])).
% 4.37/1.71  tff(c_824, plain, (![A_247, D_248]: (v1_funct_1(k8_funct_2(A_247, '#skF_1', '#skF_3', D_248, '#skF_5')) | ~m1_subset_1(D_248, k1_zfmisc_1(k2_zfmisc_1(A_247, '#skF_1'))) | ~v1_funct_2(D_248, A_247, '#skF_1') | ~v1_funct_1(D_248))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_815])).
% 4.37/1.71  tff(c_827, plain, (v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_824])).
% 4.37/1.71  tff(c_830, plain, (v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_827])).
% 4.37/1.71  tff(c_832, plain, (![B_252, A_254, E_253, D_255, C_251]: (v1_funct_2(k8_funct_2(A_254, B_252, C_251, D_255, E_253), A_254, C_251) | ~m1_subset_1(E_253, k1_zfmisc_1(k2_zfmisc_1(B_252, C_251))) | ~v1_funct_1(E_253) | ~m1_subset_1(D_255, k1_zfmisc_1(k2_zfmisc_1(A_254, B_252))) | ~v1_funct_2(D_255, A_254, B_252) | ~v1_funct_1(D_255))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.37/1.71  tff(c_834, plain, (![A_254, D_255]: (v1_funct_2(k8_funct_2(A_254, '#skF_1', '#skF_3', D_255, '#skF_5'), A_254, '#skF_3') | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_255, k1_zfmisc_1(k2_zfmisc_1(A_254, '#skF_1'))) | ~v1_funct_2(D_255, A_254, '#skF_1') | ~v1_funct_1(D_255))), inference(resolution, [status(thm)], [c_44, c_832])).
% 4.37/1.71  tff(c_843, plain, (![A_256, D_257]: (v1_funct_2(k8_funct_2(A_256, '#skF_1', '#skF_3', D_257, '#skF_5'), A_256, '#skF_3') | ~m1_subset_1(D_257, k1_zfmisc_1(k2_zfmisc_1(A_256, '#skF_1'))) | ~v1_funct_2(D_257, A_256, '#skF_1') | ~v1_funct_1(D_257))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_834])).
% 4.37/1.71  tff(c_845, plain, (v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_843])).
% 4.37/1.71  tff(c_848, plain, (v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_845])).
% 4.37/1.71  tff(c_851, plain, (![B_261, A_263, D_264, E_262, C_260]: (m1_subset_1(k8_funct_2(A_263, B_261, C_260, D_264, E_262), k1_zfmisc_1(k2_zfmisc_1(A_263, C_260))) | ~m1_subset_1(E_262, k1_zfmisc_1(k2_zfmisc_1(B_261, C_260))) | ~v1_funct_1(E_262) | ~m1_subset_1(D_264, k1_zfmisc_1(k2_zfmisc_1(A_263, B_261))) | ~v1_funct_2(D_264, A_263, B_261) | ~v1_funct_1(D_264))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.37/1.71  tff(c_1012, plain, (![D_296, A_294, B_297, E_298, C_295]: (k1_relset_1(A_294, C_295, k8_funct_2(A_294, B_297, C_295, D_296, E_298))=k1_relat_1(k8_funct_2(A_294, B_297, C_295, D_296, E_298)) | ~m1_subset_1(E_298, k1_zfmisc_1(k2_zfmisc_1(B_297, C_295))) | ~v1_funct_1(E_298) | ~m1_subset_1(D_296, k1_zfmisc_1(k2_zfmisc_1(A_294, B_297))) | ~v1_funct_2(D_296, A_294, B_297) | ~v1_funct_1(D_296))), inference(resolution, [status(thm)], [c_851, c_20])).
% 4.37/1.71  tff(c_1016, plain, (![A_294, D_296]: (k1_relset_1(A_294, '#skF_3', k8_funct_2(A_294, '#skF_1', '#skF_3', D_296, '#skF_5'))=k1_relat_1(k8_funct_2(A_294, '#skF_1', '#skF_3', D_296, '#skF_5')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_296, k1_zfmisc_1(k2_zfmisc_1(A_294, '#skF_1'))) | ~v1_funct_2(D_296, A_294, '#skF_1') | ~v1_funct_1(D_296))), inference(resolution, [status(thm)], [c_44, c_1012])).
% 4.37/1.71  tff(c_1133, plain, (![A_321, D_322]: (k1_relset_1(A_321, '#skF_3', k8_funct_2(A_321, '#skF_1', '#skF_3', D_322, '#skF_5'))=k1_relat_1(k8_funct_2(A_321, '#skF_1', '#skF_3', D_322, '#skF_5')) | ~m1_subset_1(D_322, k1_zfmisc_1(k2_zfmisc_1(A_321, '#skF_1'))) | ~v1_funct_2(D_322, A_321, '#skF_1') | ~v1_funct_1(D_322))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1016])).
% 4.37/1.71  tff(c_1138, plain, (k1_relset_1('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))=k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_1133])).
% 4.37/1.71  tff(c_1142, plain, (k1_relset_1('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))=k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1138])).
% 4.37/1.71  tff(c_1159, plain, (![B_34, D_43, F_49]: (k1_funct_1(k8_funct_2(B_34, '#skF_2', '#skF_3', D_43, k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')), F_49)=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_funct_1(D_43, F_49)) | k1_xboole_0=B_34 | ~r1_tarski(k2_relset_1(B_34, '#skF_2', D_43), k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(F_49, B_34) | ~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_43, k1_zfmisc_1(k2_zfmisc_1(B_34, '#skF_2'))) | ~v1_funct_2(D_43, B_34, '#skF_2') | ~v1_funct_1(D_43) | v1_xboole_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1142, c_36])).
% 4.37/1.71  tff(c_1163, plain, (![B_34, D_43, F_49]: (k1_funct_1(k8_funct_2(B_34, '#skF_2', '#skF_3', D_43, k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')), F_49)=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_funct_1(D_43, F_49)) | k1_xboole_0=B_34 | ~r1_tarski(k2_relset_1(B_34, '#skF_2', D_43), k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(F_49, B_34) | ~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1(D_43, k1_zfmisc_1(k2_zfmisc_1(B_34, '#skF_2'))) | ~v1_funct_2(D_43, B_34, '#skF_2') | ~v1_funct_1(D_43) | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_830, c_1159])).
% 4.37/1.71  tff(c_1164, plain, (![B_34, D_43, F_49]: (k1_funct_1(k8_funct_2(B_34, '#skF_2', '#skF_3', D_43, k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')), F_49)=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_funct_1(D_43, F_49)) | k1_xboole_0=B_34 | ~r1_tarski(k2_relset_1(B_34, '#skF_2', D_43), k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(F_49, B_34) | ~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1(D_43, k1_zfmisc_1(k2_zfmisc_1(B_34, '#skF_2'))) | ~v1_funct_2(D_43, B_34, '#skF_2') | ~v1_funct_1(D_43))), inference(negUnitSimplification, [status(thm)], [c_54, c_1163])).
% 4.37/1.71  tff(c_1187, plain, (~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_1164])).
% 4.37/1.71  tff(c_1190, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_1187])).
% 4.37/1.71  tff(c_1194, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_1190])).
% 4.37/1.71  tff(c_1196, plain, (m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_1164])).
% 4.37/1.71  tff(c_788, plain, (![A_236, B_237, C_238, D_239]: (k3_funct_2(A_236, B_237, C_238, D_239)=k1_funct_1(C_238, D_239) | ~m1_subset_1(D_239, A_236) | ~m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1(A_236, B_237))) | ~v1_funct_2(C_238, A_236, B_237) | ~v1_funct_1(C_238) | v1_xboole_0(A_236))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.37/1.71  tff(c_794, plain, (![B_237, C_238]: (k3_funct_2('#skF_2', B_237, C_238, '#skF_6')=k1_funct_1(C_238, '#skF_6') | ~m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_237))) | ~v1_funct_2(C_238, '#skF_2', B_237) | ~v1_funct_1(C_238) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_788])).
% 4.37/1.71  tff(c_799, plain, (![B_237, C_238]: (k3_funct_2('#skF_2', B_237, C_238, '#skF_6')=k1_funct_1(C_238, '#skF_6') | ~m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_237))) | ~v1_funct_2(C_238, '#skF_2', B_237) | ~v1_funct_1(C_238))), inference(negUnitSimplification, [status(thm)], [c_54, c_794])).
% 4.37/1.71  tff(c_1215, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6') | ~v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3') | ~v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_1196, c_799])).
% 4.37/1.71  tff(c_1259, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_830, c_848, c_1215])).
% 4.37/1.71  tff(c_800, plain, (![B_240, C_241]: (k3_funct_2('#skF_2', B_240, C_241, '#skF_6')=k1_funct_1(C_241, '#skF_6') | ~m1_subset_1(C_241, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_240))) | ~v1_funct_2(C_241, '#skF_2', B_240) | ~v1_funct_1(C_241))), inference(negUnitSimplification, [status(thm)], [c_54, c_794])).
% 4.37/1.71  tff(c_803, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_800])).
% 4.37/1.71  tff(c_806, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_803])).
% 4.37/1.71  tff(c_807, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_806, c_38])).
% 4.37/1.71  tff(c_1272, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1259, c_807])).
% 4.37/1.71  tff(c_1279, plain, (~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1067, c_1272])).
% 4.37/1.71  tff(c_1283, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_1279])).
% 4.37/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.37/1.71  
% 4.37/1.71  Inference rules
% 4.37/1.71  ----------------------
% 4.37/1.71  #Ref     : 0
% 4.37/1.71  #Sup     : 255
% 4.37/1.71  #Fact    : 0
% 4.37/1.71  #Define  : 0
% 4.37/1.71  #Split   : 18
% 4.37/1.71  #Chain   : 0
% 4.37/1.71  #Close   : 0
% 4.37/1.71  
% 4.37/1.71  Ordering : KBO
% 4.37/1.71  
% 4.37/1.71  Simplification rules
% 4.37/1.71  ----------------------
% 4.37/1.71  #Subsume      : 4
% 4.37/1.71  #Demod        : 199
% 4.37/1.71  #Tautology    : 58
% 4.37/1.71  #SimpNegUnit  : 17
% 4.37/1.71  #BackRed      : 11
% 4.37/1.71  
% 4.37/1.72  #Partial instantiations: 0
% 4.37/1.72  #Strategies tried      : 1
% 4.37/1.72  
% 4.37/1.72  Timing (in seconds)
% 4.37/1.72  ----------------------
% 4.37/1.72  Preprocessing        : 0.35
% 4.37/1.72  Parsing              : 0.18
% 4.37/1.72  CNF conversion       : 0.03
% 4.37/1.72  Main loop            : 0.56
% 4.37/1.72  Inferencing          : 0.20
% 4.37/1.72  Reduction            : 0.19
% 4.37/1.72  Demodulation         : 0.13
% 4.37/1.72  BG Simplification    : 0.03
% 4.37/1.72  Subsumption          : 0.10
% 4.37/1.72  Abstraction          : 0.03
% 4.37/1.72  MUC search           : 0.00
% 4.37/1.72  Cooper               : 0.00
% 4.37/1.72  Total                : 0.99
% 4.37/1.72  Index Insertion      : 0.00
% 4.37/1.72  Index Deletion       : 0.00
% 4.37/1.72  Index Matching       : 0.00
% 4.37/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
