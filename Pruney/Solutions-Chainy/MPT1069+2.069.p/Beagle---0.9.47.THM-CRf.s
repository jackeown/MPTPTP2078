%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:55 EST 2020

% Result     : Theorem 4.05s
% Output     : CNFRefutation 4.15s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 291 expanded)
%              Number of leaves         :   40 ( 119 expanded)
%              Depth                    :   14
%              Number of atoms          :  241 (1063 expanded)
%              Number of equality atoms :   51 ( 209 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_138,negated_conjecture,(
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

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_101,axiom,(
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

tff(f_56,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_113,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_36,plain,(
    m1_subset_1('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_46,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_44,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_38,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_112,plain,(
    ! [A_80,B_81,C_82] :
      ( k1_relset_1(A_80,B_81,C_82) = k1_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_120,plain,(
    k1_relset_1('#skF_4','#skF_2','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_112])).

tff(c_34,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),k1_relset_1('#skF_4','#skF_2','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_121,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_34])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_40,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_707,plain,(
    ! [C_194,A_192,E_196,F_193,D_197,B_195] :
      ( k1_funct_1(k8_funct_2(B_195,C_194,A_192,D_197,E_196),F_193) = k1_funct_1(E_196,k1_funct_1(D_197,F_193))
      | k1_xboole_0 = B_195
      | ~ r1_tarski(k2_relset_1(B_195,C_194,D_197),k1_relset_1(C_194,A_192,E_196))
      | ~ m1_subset_1(F_193,B_195)
      | ~ m1_subset_1(E_196,k1_zfmisc_1(k2_zfmisc_1(C_194,A_192)))
      | ~ v1_funct_1(E_196)
      | ~ m1_subset_1(D_197,k1_zfmisc_1(k2_zfmisc_1(B_195,C_194)))
      | ~ v1_funct_2(D_197,B_195,C_194)
      | ~ v1_funct_1(D_197)
      | v1_xboole_0(C_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_711,plain,(
    ! [B_195,D_197,F_193] :
      ( k1_funct_1(k8_funct_2(B_195,'#skF_4','#skF_2',D_197,'#skF_6'),F_193) = k1_funct_1('#skF_6',k1_funct_1(D_197,F_193))
      | k1_xboole_0 = B_195
      | ~ r1_tarski(k2_relset_1(B_195,'#skF_4',D_197),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(F_193,B_195)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(D_197,k1_zfmisc_1(k2_zfmisc_1(B_195,'#skF_4')))
      | ~ v1_funct_2(D_197,B_195,'#skF_4')
      | ~ v1_funct_1(D_197)
      | v1_xboole_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_707])).

tff(c_715,plain,(
    ! [B_195,D_197,F_193] :
      ( k1_funct_1(k8_funct_2(B_195,'#skF_4','#skF_2',D_197,'#skF_6'),F_193) = k1_funct_1('#skF_6',k1_funct_1(D_197,F_193))
      | k1_xboole_0 = B_195
      | ~ r1_tarski(k2_relset_1(B_195,'#skF_4',D_197),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(F_193,B_195)
      | ~ m1_subset_1(D_197,k1_zfmisc_1(k2_zfmisc_1(B_195,'#skF_4')))
      | ~ v1_funct_2(D_197,B_195,'#skF_4')
      | ~ v1_funct_1(D_197)
      | v1_xboole_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_711])).

tff(c_1137,plain,(
    ! [B_253,D_254,F_255] :
      ( k1_funct_1(k8_funct_2(B_253,'#skF_4','#skF_2',D_254,'#skF_6'),F_255) = k1_funct_1('#skF_6',k1_funct_1(D_254,F_255))
      | k1_xboole_0 = B_253
      | ~ r1_tarski(k2_relset_1(B_253,'#skF_4',D_254),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(F_255,B_253)
      | ~ m1_subset_1(D_254,k1_zfmisc_1(k2_zfmisc_1(B_253,'#skF_4')))
      | ~ v1_funct_2(D_254,B_253,'#skF_4')
      | ~ v1_funct_1(D_254) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_715])).

tff(c_1139,plain,(
    ! [F_255] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),F_255) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',F_255))
      | k1_xboole_0 = '#skF_3'
      | ~ m1_subset_1(F_255,'#skF_3')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_121,c_1137])).

tff(c_1142,plain,(
    ! [F_255] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),F_255) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',F_255))
      | k1_xboole_0 = '#skF_3'
      | ~ m1_subset_1(F_255,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_1139])).

tff(c_1143,plain,(
    ! [F_255] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),F_255) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',F_255))
      | ~ m1_subset_1(F_255,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1142])).

tff(c_16,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_60,plain,(
    ! [B_62,A_63] :
      ( v1_relat_1(B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_63))
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_63,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_42,c_60])).

tff(c_69,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_63])).

tff(c_103,plain,(
    ! [C_77,B_78,A_79] :
      ( v5_relat_1(C_77,B_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_79,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_110,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_103])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r2_hidden(A_8,B_9)
      | v1_xboole_0(B_9)
      | ~ m1_subset_1(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_147,plain,(
    ! [A_91,B_92,C_93] :
      ( k7_partfun1(A_91,B_92,C_93) = k1_funct_1(B_92,C_93)
      | ~ r2_hidden(C_93,k1_relat_1(B_92))
      | ~ v1_funct_1(B_92)
      | ~ v5_relat_1(B_92,A_91)
      | ~ v1_relat_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_696,plain,(
    ! [A_189,B_190,A_191] :
      ( k7_partfun1(A_189,B_190,A_191) = k1_funct_1(B_190,A_191)
      | ~ v1_funct_1(B_190)
      | ~ v5_relat_1(B_190,A_189)
      | ~ v1_relat_1(B_190)
      | v1_xboole_0(k1_relat_1(B_190))
      | ~ m1_subset_1(A_191,k1_relat_1(B_190)) ) ),
    inference(resolution,[status(thm)],[c_12,c_147])).

tff(c_700,plain,(
    ! [A_191] :
      ( k7_partfun1('#skF_4','#skF_5',A_191) = k1_funct_1('#skF_5',A_191)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | v1_xboole_0(k1_relat_1('#skF_5'))
      | ~ m1_subset_1(A_191,k1_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_110,c_696])).

tff(c_706,plain,(
    ! [A_191] :
      ( k7_partfun1('#skF_4','#skF_5',A_191) = k1_funct_1('#skF_5',A_191)
      | v1_xboole_0(k1_relat_1('#skF_5'))
      | ~ m1_subset_1(A_191,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_46,c_700])).

tff(c_1145,plain,(
    v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_706])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_50,plain,(
    ! [B_59,A_60] :
      ( ~ v1_xboole_0(B_59)
      | B_59 = A_60
      | ~ v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_53,plain,(
    ! [A_60] :
      ( k1_xboole_0 = A_60
      | ~ v1_xboole_0(A_60) ) ),
    inference(resolution,[status(thm)],[c_8,c_50])).

tff(c_1151,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1145,c_53])).

tff(c_119,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_112])).

tff(c_709,plain,(
    ! [B_195,D_197,F_193] :
      ( k1_funct_1(k8_funct_2(B_195,'#skF_3','#skF_4',D_197,'#skF_5'),F_193) = k1_funct_1('#skF_5',k1_funct_1(D_197,F_193))
      | k1_xboole_0 = B_195
      | ~ r1_tarski(k2_relset_1(B_195,'#skF_3',D_197),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(F_193,B_195)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_197,k1_zfmisc_1(k2_zfmisc_1(B_195,'#skF_3')))
      | ~ v1_funct_2(D_197,B_195,'#skF_3')
      | ~ v1_funct_1(D_197)
      | v1_xboole_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_707])).

tff(c_713,plain,(
    ! [B_195,D_197,F_193] :
      ( k1_funct_1(k8_funct_2(B_195,'#skF_3','#skF_4',D_197,'#skF_5'),F_193) = k1_funct_1('#skF_5',k1_funct_1(D_197,F_193))
      | k1_xboole_0 = B_195
      | ~ r1_tarski(k2_relset_1(B_195,'#skF_3',D_197),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(F_193,B_195)
      | ~ m1_subset_1(D_197,k1_zfmisc_1(k2_zfmisc_1(B_195,'#skF_3')))
      | ~ v1_funct_2(D_197,B_195,'#skF_3')
      | ~ v1_funct_1(D_197)
      | v1_xboole_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_709])).

tff(c_1295,plain,(
    ! [B_195,D_197,F_193] :
      ( k1_funct_1(k8_funct_2(B_195,'#skF_3','#skF_4',D_197,'#skF_5'),F_193) = k1_funct_1('#skF_5',k1_funct_1(D_197,F_193))
      | k1_xboole_0 = B_195
      | ~ r1_tarski(k2_relset_1(B_195,'#skF_3',D_197),k1_xboole_0)
      | ~ m1_subset_1(F_193,B_195)
      | ~ m1_subset_1(D_197,k1_zfmisc_1(k2_zfmisc_1(B_195,'#skF_3')))
      | ~ v1_funct_2(D_197,B_195,'#skF_3')
      | ~ v1_funct_1(D_197)
      | v1_xboole_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1151,c_713])).

tff(c_1296,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1295])).

tff(c_1299,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1296,c_53])).

tff(c_1305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1299])).

tff(c_1307,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1295])).

tff(c_111,plain,(
    v5_relat_1('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_103])).

tff(c_66,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_60])).

tff(c_72,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_66])).

tff(c_642,plain,(
    ! [D_171,C_172,A_173,B_174] :
      ( r2_hidden(k1_funct_1(D_171,C_172),k2_relset_1(A_173,B_174,D_171))
      | k1_xboole_0 = B_174
      | ~ r2_hidden(C_172,A_173)
      | ~ m1_subset_1(D_171,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174)))
      | ~ v1_funct_2(D_171,A_173,B_174)
      | ~ v1_funct_1(D_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1268,plain,(
    ! [B_274,D_273,C_275,A_272,B_276] :
      ( r2_hidden(k1_funct_1(D_273,C_275),B_276)
      | ~ r1_tarski(k2_relset_1(A_272,B_274,D_273),B_276)
      | k1_xboole_0 = B_274
      | ~ r2_hidden(C_275,A_272)
      | ~ m1_subset_1(D_273,k1_zfmisc_1(k2_zfmisc_1(A_272,B_274)))
      | ~ v1_funct_2(D_273,A_272,B_274)
      | ~ v1_funct_1(D_273) ) ),
    inference(resolution,[status(thm)],[c_642,c_2])).

tff(c_1270,plain,(
    ! [C_275] :
      ( r2_hidden(k1_funct_1('#skF_5',C_275),k1_relat_1('#skF_6'))
      | k1_xboole_0 = '#skF_4'
      | ~ r2_hidden(C_275,'#skF_3')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_121,c_1268])).

tff(c_1276,plain,(
    ! [C_275] :
      ( r2_hidden(k1_funct_1('#skF_5',C_275),k1_relat_1('#skF_6'))
      | k1_xboole_0 = '#skF_4'
      | ~ r2_hidden(C_275,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_1270])).

tff(c_1278,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1276])).

tff(c_1289,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1278,c_8])).

tff(c_1292,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1289])).

tff(c_1308,plain,(
    ! [C_277] :
      ( r2_hidden(k1_funct_1('#skF_5',C_277),k1_relat_1('#skF_6'))
      | ~ r2_hidden(C_277,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_1276])).

tff(c_24,plain,(
    ! [A_21,B_22,C_24] :
      ( k7_partfun1(A_21,B_22,C_24) = k1_funct_1(B_22,C_24)
      | ~ r2_hidden(C_24,k1_relat_1(B_22))
      | ~ v1_funct_1(B_22)
      | ~ v5_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1310,plain,(
    ! [A_21,C_277] :
      ( k7_partfun1(A_21,'#skF_6',k1_funct_1('#skF_5',C_277)) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',C_277))
      | ~ v1_funct_1('#skF_6')
      | ~ v5_relat_1('#skF_6',A_21)
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden(C_277,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1308,c_24])).

tff(c_1350,plain,(
    ! [A_287,C_288] :
      ( k7_partfun1(A_287,'#skF_6',k1_funct_1('#skF_5',C_288)) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',C_288))
      | ~ v5_relat_1('#skF_6',A_287)
      | ~ r2_hidden(C_288,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_40,c_1310])).

tff(c_30,plain,(
    k7_partfun1('#skF_2','#skF_6',k1_funct_1('#skF_5','#skF_7')) != k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1356,plain,
    ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7'))
    | ~ v5_relat_1('#skF_6','#skF_2')
    | ~ r2_hidden('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1350,c_30])).

tff(c_1362,plain,
    ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7'))
    | ~ r2_hidden('#skF_7','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_1356])).

tff(c_1364,plain,(
    ~ r2_hidden('#skF_7','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1362])).

tff(c_1367,plain,
    ( v1_xboole_0('#skF_3')
    | ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_1364])).

tff(c_1370,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1367])).

tff(c_1372,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1307,c_1370])).

tff(c_1373,plain,(
    k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1362])).

tff(c_1400,plain,(
    ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1143,c_1373])).

tff(c_1404,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1400])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:34:25 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.05/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.05/1.67  
% 4.05/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.05/1.67  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.05/1.67  
% 4.05/1.67  %Foreground sorts:
% 4.05/1.67  
% 4.05/1.67  
% 4.05/1.67  %Background operators:
% 4.05/1.67  
% 4.05/1.67  
% 4.05/1.67  %Foreground operators:
% 4.05/1.67  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.05/1.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.05/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.05/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.05/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.05/1.67  tff('#skF_7', type, '#skF_7': $i).
% 4.05/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.05/1.67  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 4.05/1.67  tff('#skF_5', type, '#skF_5': $i).
% 4.05/1.67  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.05/1.67  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 4.05/1.67  tff('#skF_6', type, '#skF_6': $i).
% 4.05/1.67  tff('#skF_2', type, '#skF_2': $i).
% 4.05/1.67  tff('#skF_3', type, '#skF_3': $i).
% 4.05/1.67  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.05/1.67  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.05/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.05/1.67  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.05/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.05/1.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.05/1.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.05/1.67  tff('#skF_4', type, '#skF_4': $i).
% 4.05/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.05/1.67  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.05/1.67  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.05/1.67  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.05/1.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.05/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.05/1.67  
% 4.15/1.69  tff(f_138, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 4.15/1.69  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.15/1.69  tff(f_101, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 4.15/1.69  tff(f_56, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.15/1.69  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.15/1.69  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.15/1.69  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.15/1.69  tff(f_77, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 4.15/1.69  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.15/1.69  tff(f_41, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 4.15/1.69  tff(f_113, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 4.15/1.69  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.15/1.69  tff(c_36, plain, (m1_subset_1('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.15/1.69  tff(c_32, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.15/1.69  tff(c_46, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.15/1.69  tff(c_44, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.15/1.69  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.15/1.69  tff(c_38, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.15/1.69  tff(c_112, plain, (![A_80, B_81, C_82]: (k1_relset_1(A_80, B_81, C_82)=k1_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.15/1.69  tff(c_120, plain, (k1_relset_1('#skF_4', '#skF_2', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_38, c_112])).
% 4.15/1.69  tff(c_34, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), k1_relset_1('#skF_4', '#skF_2', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.15/1.69  tff(c_121, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_34])).
% 4.15/1.69  tff(c_48, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.15/1.69  tff(c_40, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.15/1.69  tff(c_707, plain, (![C_194, A_192, E_196, F_193, D_197, B_195]: (k1_funct_1(k8_funct_2(B_195, C_194, A_192, D_197, E_196), F_193)=k1_funct_1(E_196, k1_funct_1(D_197, F_193)) | k1_xboole_0=B_195 | ~r1_tarski(k2_relset_1(B_195, C_194, D_197), k1_relset_1(C_194, A_192, E_196)) | ~m1_subset_1(F_193, B_195) | ~m1_subset_1(E_196, k1_zfmisc_1(k2_zfmisc_1(C_194, A_192))) | ~v1_funct_1(E_196) | ~m1_subset_1(D_197, k1_zfmisc_1(k2_zfmisc_1(B_195, C_194))) | ~v1_funct_2(D_197, B_195, C_194) | ~v1_funct_1(D_197) | v1_xboole_0(C_194))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.15/1.69  tff(c_711, plain, (![B_195, D_197, F_193]: (k1_funct_1(k8_funct_2(B_195, '#skF_4', '#skF_2', D_197, '#skF_6'), F_193)=k1_funct_1('#skF_6', k1_funct_1(D_197, F_193)) | k1_xboole_0=B_195 | ~r1_tarski(k2_relset_1(B_195, '#skF_4', D_197), k1_relat_1('#skF_6')) | ~m1_subset_1(F_193, B_195) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1(D_197, k1_zfmisc_1(k2_zfmisc_1(B_195, '#skF_4'))) | ~v1_funct_2(D_197, B_195, '#skF_4') | ~v1_funct_1(D_197) | v1_xboole_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_120, c_707])).
% 4.15/1.69  tff(c_715, plain, (![B_195, D_197, F_193]: (k1_funct_1(k8_funct_2(B_195, '#skF_4', '#skF_2', D_197, '#skF_6'), F_193)=k1_funct_1('#skF_6', k1_funct_1(D_197, F_193)) | k1_xboole_0=B_195 | ~r1_tarski(k2_relset_1(B_195, '#skF_4', D_197), k1_relat_1('#skF_6')) | ~m1_subset_1(F_193, B_195) | ~m1_subset_1(D_197, k1_zfmisc_1(k2_zfmisc_1(B_195, '#skF_4'))) | ~v1_funct_2(D_197, B_195, '#skF_4') | ~v1_funct_1(D_197) | v1_xboole_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_711])).
% 4.15/1.69  tff(c_1137, plain, (![B_253, D_254, F_255]: (k1_funct_1(k8_funct_2(B_253, '#skF_4', '#skF_2', D_254, '#skF_6'), F_255)=k1_funct_1('#skF_6', k1_funct_1(D_254, F_255)) | k1_xboole_0=B_253 | ~r1_tarski(k2_relset_1(B_253, '#skF_4', D_254), k1_relat_1('#skF_6')) | ~m1_subset_1(F_255, B_253) | ~m1_subset_1(D_254, k1_zfmisc_1(k2_zfmisc_1(B_253, '#skF_4'))) | ~v1_funct_2(D_254, B_253, '#skF_4') | ~v1_funct_1(D_254))), inference(negUnitSimplification, [status(thm)], [c_48, c_715])).
% 4.15/1.69  tff(c_1139, plain, (![F_255]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), F_255)=k1_funct_1('#skF_6', k1_funct_1('#skF_5', F_255)) | k1_xboole_0='#skF_3' | ~m1_subset_1(F_255, '#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_121, c_1137])).
% 4.15/1.69  tff(c_1142, plain, (![F_255]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), F_255)=k1_funct_1('#skF_6', k1_funct_1('#skF_5', F_255)) | k1_xboole_0='#skF_3' | ~m1_subset_1(F_255, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_1139])).
% 4.15/1.69  tff(c_1143, plain, (![F_255]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), F_255)=k1_funct_1('#skF_6', k1_funct_1('#skF_5', F_255)) | ~m1_subset_1(F_255, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_32, c_1142])).
% 4.15/1.69  tff(c_16, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.15/1.69  tff(c_60, plain, (![B_62, A_63]: (v1_relat_1(B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(A_63)) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.15/1.69  tff(c_63, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_42, c_60])).
% 4.15/1.69  tff(c_69, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_63])).
% 4.15/1.69  tff(c_103, plain, (![C_77, B_78, A_79]: (v5_relat_1(C_77, B_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_79, B_78))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.15/1.69  tff(c_110, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_103])).
% 4.15/1.69  tff(c_12, plain, (![A_8, B_9]: (r2_hidden(A_8, B_9) | v1_xboole_0(B_9) | ~m1_subset_1(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.15/1.69  tff(c_147, plain, (![A_91, B_92, C_93]: (k7_partfun1(A_91, B_92, C_93)=k1_funct_1(B_92, C_93) | ~r2_hidden(C_93, k1_relat_1(B_92)) | ~v1_funct_1(B_92) | ~v5_relat_1(B_92, A_91) | ~v1_relat_1(B_92))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.15/1.69  tff(c_696, plain, (![A_189, B_190, A_191]: (k7_partfun1(A_189, B_190, A_191)=k1_funct_1(B_190, A_191) | ~v1_funct_1(B_190) | ~v5_relat_1(B_190, A_189) | ~v1_relat_1(B_190) | v1_xboole_0(k1_relat_1(B_190)) | ~m1_subset_1(A_191, k1_relat_1(B_190)))), inference(resolution, [status(thm)], [c_12, c_147])).
% 4.15/1.69  tff(c_700, plain, (![A_191]: (k7_partfun1('#skF_4', '#skF_5', A_191)=k1_funct_1('#skF_5', A_191) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | v1_xboole_0(k1_relat_1('#skF_5')) | ~m1_subset_1(A_191, k1_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_110, c_696])).
% 4.15/1.69  tff(c_706, plain, (![A_191]: (k7_partfun1('#skF_4', '#skF_5', A_191)=k1_funct_1('#skF_5', A_191) | v1_xboole_0(k1_relat_1('#skF_5')) | ~m1_subset_1(A_191, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_46, c_700])).
% 4.15/1.69  tff(c_1145, plain, (v1_xboole_0(k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_706])).
% 4.15/1.69  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.15/1.69  tff(c_50, plain, (![B_59, A_60]: (~v1_xboole_0(B_59) | B_59=A_60 | ~v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.15/1.69  tff(c_53, plain, (![A_60]: (k1_xboole_0=A_60 | ~v1_xboole_0(A_60))), inference(resolution, [status(thm)], [c_8, c_50])).
% 4.15/1.69  tff(c_1151, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_1145, c_53])).
% 4.15/1.69  tff(c_119, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_112])).
% 4.15/1.69  tff(c_709, plain, (![B_195, D_197, F_193]: (k1_funct_1(k8_funct_2(B_195, '#skF_3', '#skF_4', D_197, '#skF_5'), F_193)=k1_funct_1('#skF_5', k1_funct_1(D_197, F_193)) | k1_xboole_0=B_195 | ~r1_tarski(k2_relset_1(B_195, '#skF_3', D_197), k1_relat_1('#skF_5')) | ~m1_subset_1(F_193, B_195) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_197, k1_zfmisc_1(k2_zfmisc_1(B_195, '#skF_3'))) | ~v1_funct_2(D_197, B_195, '#skF_3') | ~v1_funct_1(D_197) | v1_xboole_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_119, c_707])).
% 4.15/1.69  tff(c_713, plain, (![B_195, D_197, F_193]: (k1_funct_1(k8_funct_2(B_195, '#skF_3', '#skF_4', D_197, '#skF_5'), F_193)=k1_funct_1('#skF_5', k1_funct_1(D_197, F_193)) | k1_xboole_0=B_195 | ~r1_tarski(k2_relset_1(B_195, '#skF_3', D_197), k1_relat_1('#skF_5')) | ~m1_subset_1(F_193, B_195) | ~m1_subset_1(D_197, k1_zfmisc_1(k2_zfmisc_1(B_195, '#skF_3'))) | ~v1_funct_2(D_197, B_195, '#skF_3') | ~v1_funct_1(D_197) | v1_xboole_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_709])).
% 4.15/1.69  tff(c_1295, plain, (![B_195, D_197, F_193]: (k1_funct_1(k8_funct_2(B_195, '#skF_3', '#skF_4', D_197, '#skF_5'), F_193)=k1_funct_1('#skF_5', k1_funct_1(D_197, F_193)) | k1_xboole_0=B_195 | ~r1_tarski(k2_relset_1(B_195, '#skF_3', D_197), k1_xboole_0) | ~m1_subset_1(F_193, B_195) | ~m1_subset_1(D_197, k1_zfmisc_1(k2_zfmisc_1(B_195, '#skF_3'))) | ~v1_funct_2(D_197, B_195, '#skF_3') | ~v1_funct_1(D_197) | v1_xboole_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1151, c_713])).
% 4.15/1.69  tff(c_1296, plain, (v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_1295])).
% 4.15/1.69  tff(c_1299, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1296, c_53])).
% 4.15/1.69  tff(c_1305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_1299])).
% 4.15/1.69  tff(c_1307, plain, (~v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_1295])).
% 4.15/1.69  tff(c_111, plain, (v5_relat_1('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_103])).
% 4.15/1.69  tff(c_66, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_60])).
% 4.15/1.69  tff(c_72, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_66])).
% 4.15/1.69  tff(c_642, plain, (![D_171, C_172, A_173, B_174]: (r2_hidden(k1_funct_1(D_171, C_172), k2_relset_1(A_173, B_174, D_171)) | k1_xboole_0=B_174 | ~r2_hidden(C_172, A_173) | ~m1_subset_1(D_171, k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))) | ~v1_funct_2(D_171, A_173, B_174) | ~v1_funct_1(D_171))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.15/1.69  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.15/1.69  tff(c_1268, plain, (![B_274, D_273, C_275, A_272, B_276]: (r2_hidden(k1_funct_1(D_273, C_275), B_276) | ~r1_tarski(k2_relset_1(A_272, B_274, D_273), B_276) | k1_xboole_0=B_274 | ~r2_hidden(C_275, A_272) | ~m1_subset_1(D_273, k1_zfmisc_1(k2_zfmisc_1(A_272, B_274))) | ~v1_funct_2(D_273, A_272, B_274) | ~v1_funct_1(D_273))), inference(resolution, [status(thm)], [c_642, c_2])).
% 4.15/1.69  tff(c_1270, plain, (![C_275]: (r2_hidden(k1_funct_1('#skF_5', C_275), k1_relat_1('#skF_6')) | k1_xboole_0='#skF_4' | ~r2_hidden(C_275, '#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_121, c_1268])).
% 4.15/1.69  tff(c_1276, plain, (![C_275]: (r2_hidden(k1_funct_1('#skF_5', C_275), k1_relat_1('#skF_6')) | k1_xboole_0='#skF_4' | ~r2_hidden(C_275, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_1270])).
% 4.15/1.69  tff(c_1278, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_1276])).
% 4.15/1.69  tff(c_1289, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1278, c_8])).
% 4.15/1.69  tff(c_1292, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_1289])).
% 4.15/1.69  tff(c_1308, plain, (![C_277]: (r2_hidden(k1_funct_1('#skF_5', C_277), k1_relat_1('#skF_6')) | ~r2_hidden(C_277, '#skF_3'))), inference(splitRight, [status(thm)], [c_1276])).
% 4.15/1.69  tff(c_24, plain, (![A_21, B_22, C_24]: (k7_partfun1(A_21, B_22, C_24)=k1_funct_1(B_22, C_24) | ~r2_hidden(C_24, k1_relat_1(B_22)) | ~v1_funct_1(B_22) | ~v5_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.15/1.69  tff(c_1310, plain, (![A_21, C_277]: (k7_partfun1(A_21, '#skF_6', k1_funct_1('#skF_5', C_277))=k1_funct_1('#skF_6', k1_funct_1('#skF_5', C_277)) | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', A_21) | ~v1_relat_1('#skF_6') | ~r2_hidden(C_277, '#skF_3'))), inference(resolution, [status(thm)], [c_1308, c_24])).
% 4.15/1.69  tff(c_1350, plain, (![A_287, C_288]: (k7_partfun1(A_287, '#skF_6', k1_funct_1('#skF_5', C_288))=k1_funct_1('#skF_6', k1_funct_1('#skF_5', C_288)) | ~v5_relat_1('#skF_6', A_287) | ~r2_hidden(C_288, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_40, c_1310])).
% 4.15/1.69  tff(c_30, plain, (k7_partfun1('#skF_2', '#skF_6', k1_funct_1('#skF_5', '#skF_7'))!=k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.15/1.69  tff(c_1356, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7')) | ~v5_relat_1('#skF_6', '#skF_2') | ~r2_hidden('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1350, c_30])).
% 4.15/1.69  tff(c_1362, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7')) | ~r2_hidden('#skF_7', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_1356])).
% 4.15/1.69  tff(c_1364, plain, (~r2_hidden('#skF_7', '#skF_3')), inference(splitLeft, [status(thm)], [c_1362])).
% 4.15/1.69  tff(c_1367, plain, (v1_xboole_0('#skF_3') | ~m1_subset_1('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_12, c_1364])).
% 4.15/1.69  tff(c_1370, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1367])).
% 4.15/1.69  tff(c_1372, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1307, c_1370])).
% 4.15/1.69  tff(c_1373, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7'))), inference(splitRight, [status(thm)], [c_1362])).
% 4.15/1.69  tff(c_1400, plain, (~m1_subset_1('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1143, c_1373])).
% 4.15/1.69  tff(c_1404, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_1400])).
% 4.15/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.15/1.69  
% 4.15/1.69  Inference rules
% 4.15/1.69  ----------------------
% 4.15/1.69  #Ref     : 0
% 4.15/1.69  #Sup     : 281
% 4.15/1.69  #Fact    : 0
% 4.15/1.69  #Define  : 0
% 4.15/1.69  #Split   : 23
% 4.15/1.69  #Chain   : 0
% 4.15/1.69  #Close   : 0
% 4.15/1.69  
% 4.15/1.69  Ordering : KBO
% 4.15/1.69  
% 4.15/1.69  Simplification rules
% 4.15/1.69  ----------------------
% 4.15/1.69  #Subsume      : 56
% 4.15/1.69  #Demod        : 254
% 4.15/1.69  #Tautology    : 78
% 4.15/1.69  #SimpNegUnit  : 17
% 4.15/1.69  #BackRed      : 70
% 4.15/1.69  
% 4.15/1.69  #Partial instantiations: 0
% 4.15/1.69  #Strategies tried      : 1
% 4.15/1.69  
% 4.15/1.69  Timing (in seconds)
% 4.15/1.69  ----------------------
% 4.15/1.69  Preprocessing        : 0.35
% 4.15/1.69  Parsing              : 0.19
% 4.15/1.69  CNF conversion       : 0.03
% 4.15/1.69  Main loop            : 0.57
% 4.15/1.69  Inferencing          : 0.21
% 4.15/1.69  Reduction            : 0.18
% 4.15/1.69  Demodulation         : 0.12
% 4.15/1.69  BG Simplification    : 0.03
% 4.15/1.69  Subsumption          : 0.12
% 4.15/1.69  Abstraction          : 0.03
% 4.15/1.69  MUC search           : 0.00
% 4.15/1.69  Cooper               : 0.00
% 4.15/1.69  Total                : 0.96
% 4.15/1.69  Index Insertion      : 0.00
% 4.15/1.69  Index Deletion       : 0.00
% 4.15/1.69  Index Matching       : 0.00
% 4.15/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
