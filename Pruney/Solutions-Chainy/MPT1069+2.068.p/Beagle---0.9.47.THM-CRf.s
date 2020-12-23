%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:55 EST 2020

% Result     : Theorem 3.89s
% Output     : CNFRefutation 3.89s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 282 expanded)
%              Number of leaves         :   40 ( 116 expanded)
%              Depth                    :   14
%              Number of atoms          :  237 (1045 expanded)
%              Number of equality atoms :   50 ( 206 expanded)
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

tff(f_134,negated_conjecture,(
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

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_97,axiom,(
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

tff(f_52,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_109,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_36,plain,(
    m1_subset_1('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_46,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_44,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_38,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_108,plain,(
    ! [A_77,B_78,C_79] :
      ( k1_relset_1(A_77,B_78,C_79) = k1_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_116,plain,(
    k1_relset_1('#skF_4','#skF_2','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_108])).

tff(c_34,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),k1_relset_1('#skF_4','#skF_2','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_121,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_34])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_40,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1047,plain,(
    ! [C_245,D_244,E_247,F_248,A_249,B_246] :
      ( k1_funct_1(k8_funct_2(B_246,C_245,A_249,D_244,E_247),F_248) = k1_funct_1(E_247,k1_funct_1(D_244,F_248))
      | k1_xboole_0 = B_246
      | ~ r1_tarski(k2_relset_1(B_246,C_245,D_244),k1_relset_1(C_245,A_249,E_247))
      | ~ m1_subset_1(F_248,B_246)
      | ~ m1_subset_1(E_247,k1_zfmisc_1(k2_zfmisc_1(C_245,A_249)))
      | ~ v1_funct_1(E_247)
      | ~ m1_subset_1(D_244,k1_zfmisc_1(k2_zfmisc_1(B_246,C_245)))
      | ~ v1_funct_2(D_244,B_246,C_245)
      | ~ v1_funct_1(D_244)
      | v1_xboole_0(C_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1049,plain,(
    ! [B_246,D_244,F_248] :
      ( k1_funct_1(k8_funct_2(B_246,'#skF_4','#skF_2',D_244,'#skF_6'),F_248) = k1_funct_1('#skF_6',k1_funct_1(D_244,F_248))
      | k1_xboole_0 = B_246
      | ~ r1_tarski(k2_relset_1(B_246,'#skF_4',D_244),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(F_248,B_246)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(D_244,k1_zfmisc_1(k2_zfmisc_1(B_246,'#skF_4')))
      | ~ v1_funct_2(D_244,B_246,'#skF_4')
      | ~ v1_funct_1(D_244)
      | v1_xboole_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_1047])).

tff(c_1053,plain,(
    ! [B_246,D_244,F_248] :
      ( k1_funct_1(k8_funct_2(B_246,'#skF_4','#skF_2',D_244,'#skF_6'),F_248) = k1_funct_1('#skF_6',k1_funct_1(D_244,F_248))
      | k1_xboole_0 = B_246
      | ~ r1_tarski(k2_relset_1(B_246,'#skF_4',D_244),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(F_248,B_246)
      | ~ m1_subset_1(D_244,k1_zfmisc_1(k2_zfmisc_1(B_246,'#skF_4')))
      | ~ v1_funct_2(D_244,B_246,'#skF_4')
      | ~ v1_funct_1(D_244)
      | v1_xboole_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1049])).

tff(c_1080,plain,(
    ! [B_250,D_251,F_252] :
      ( k1_funct_1(k8_funct_2(B_250,'#skF_4','#skF_2',D_251,'#skF_6'),F_252) = k1_funct_1('#skF_6',k1_funct_1(D_251,F_252))
      | k1_xboole_0 = B_250
      | ~ r1_tarski(k2_relset_1(B_250,'#skF_4',D_251),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(F_252,B_250)
      | ~ m1_subset_1(D_251,k1_zfmisc_1(k2_zfmisc_1(B_250,'#skF_4')))
      | ~ v1_funct_2(D_251,B_250,'#skF_4')
      | ~ v1_funct_1(D_251) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1053])).

tff(c_1082,plain,(
    ! [F_252] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),F_252) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',F_252))
      | k1_xboole_0 = '#skF_3'
      | ~ m1_subset_1(F_252,'#skF_3')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_121,c_1080])).

tff(c_1085,plain,(
    ! [F_252] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),F_252) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',F_252))
      | k1_xboole_0 = '#skF_3'
      | ~ m1_subset_1(F_252,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_1082])).

tff(c_1086,plain,(
    ! [F_252] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),F_252) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',F_252))
      | ~ m1_subset_1(F_252,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1085])).

tff(c_16,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_56,plain,(
    ! [B_59,A_60] :
      ( v1_relat_1(B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_60))
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_59,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_42,c_56])).

tff(c_65,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_59])).

tff(c_99,plain,(
    ! [C_74,B_75,A_76] :
      ( v5_relat_1(C_74,B_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_76,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_106,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_99])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_150,plain,(
    ! [A_92,B_93,C_94] :
      ( k7_partfun1(A_92,B_93,C_94) = k1_funct_1(B_93,C_94)
      | ~ r2_hidden(C_94,k1_relat_1(B_93))
      | ~ v1_funct_1(B_93)
      | ~ v5_relat_1(B_93,A_92)
      | ~ v1_relat_1(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_665,plain,(
    ! [A_184,B_185,A_186] :
      ( k7_partfun1(A_184,B_185,A_186) = k1_funct_1(B_185,A_186)
      | ~ v1_funct_1(B_185)
      | ~ v5_relat_1(B_185,A_184)
      | ~ v1_relat_1(B_185)
      | v1_xboole_0(k1_relat_1(B_185))
      | ~ m1_subset_1(A_186,k1_relat_1(B_185)) ) ),
    inference(resolution,[status(thm)],[c_12,c_150])).

tff(c_669,plain,(
    ! [A_186] :
      ( k7_partfun1('#skF_4','#skF_5',A_186) = k1_funct_1('#skF_5',A_186)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | v1_xboole_0(k1_relat_1('#skF_5'))
      | ~ m1_subset_1(A_186,k1_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_106,c_665])).

tff(c_675,plain,(
    ! [A_186] :
      ( k7_partfun1('#skF_4','#skF_5',A_186) = k1_funct_1('#skF_5',A_186)
      | v1_xboole_0(k1_relat_1('#skF_5'))
      | ~ m1_subset_1(A_186,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_46,c_669])).

tff(c_1046,plain,(
    v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_675])).

tff(c_10,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1060,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1046,c_10])).

tff(c_115,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_108])).

tff(c_1051,plain,(
    ! [B_246,D_244,F_248] :
      ( k1_funct_1(k8_funct_2(B_246,'#skF_3','#skF_4',D_244,'#skF_5'),F_248) = k1_funct_1('#skF_5',k1_funct_1(D_244,F_248))
      | k1_xboole_0 = B_246
      | ~ r1_tarski(k2_relset_1(B_246,'#skF_3',D_244),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(F_248,B_246)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_244,k1_zfmisc_1(k2_zfmisc_1(B_246,'#skF_3')))
      | ~ v1_funct_2(D_244,B_246,'#skF_3')
      | ~ v1_funct_1(D_244)
      | v1_xboole_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_1047])).

tff(c_1056,plain,(
    ! [B_246,D_244,F_248] :
      ( k1_funct_1(k8_funct_2(B_246,'#skF_3','#skF_4',D_244,'#skF_5'),F_248) = k1_funct_1('#skF_5',k1_funct_1(D_244,F_248))
      | k1_xboole_0 = B_246
      | ~ r1_tarski(k2_relset_1(B_246,'#skF_3',D_244),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(F_248,B_246)
      | ~ m1_subset_1(D_244,k1_zfmisc_1(k2_zfmisc_1(B_246,'#skF_3')))
      | ~ v1_funct_2(D_244,B_246,'#skF_3')
      | ~ v1_funct_1(D_244)
      | v1_xboole_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_1051])).

tff(c_1248,plain,(
    ! [B_246,D_244,F_248] :
      ( k1_funct_1(k8_funct_2(B_246,'#skF_3','#skF_4',D_244,'#skF_5'),F_248) = k1_funct_1('#skF_5',k1_funct_1(D_244,F_248))
      | k1_xboole_0 = B_246
      | ~ r1_tarski(k2_relset_1(B_246,'#skF_3',D_244),k1_xboole_0)
      | ~ m1_subset_1(F_248,B_246)
      | ~ m1_subset_1(D_244,k1_zfmisc_1(k2_zfmisc_1(B_246,'#skF_3')))
      | ~ v1_funct_2(D_244,B_246,'#skF_3')
      | ~ v1_funct_1(D_244)
      | v1_xboole_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1060,c_1056])).

tff(c_1249,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1248])).

tff(c_1252,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1249,c_10])).

tff(c_1256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1252])).

tff(c_1258,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1248])).

tff(c_107,plain,(
    v5_relat_1('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_99])).

tff(c_62,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_56])).

tff(c_68,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_62])).

tff(c_638,plain,(
    ! [D_172,C_173,A_174,B_175] :
      ( r2_hidden(k1_funct_1(D_172,C_173),k2_relset_1(A_174,B_175,D_172))
      | k1_xboole_0 = B_175
      | ~ r2_hidden(C_173,A_174)
      | ~ m1_subset_1(D_172,k1_zfmisc_1(k2_zfmisc_1(A_174,B_175)))
      | ~ v1_funct_2(D_172,A_174,B_175)
      | ~ v1_funct_1(D_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1211,plain,(
    ! [A_279,B_281,B_280,C_278,D_277] :
      ( r2_hidden(k1_funct_1(D_277,C_278),B_280)
      | ~ r1_tarski(k2_relset_1(A_279,B_281,D_277),B_280)
      | k1_xboole_0 = B_281
      | ~ r2_hidden(C_278,A_279)
      | ~ m1_subset_1(D_277,k1_zfmisc_1(k2_zfmisc_1(A_279,B_281)))
      | ~ v1_funct_2(D_277,A_279,B_281)
      | ~ v1_funct_1(D_277) ) ),
    inference(resolution,[status(thm)],[c_638,c_2])).

tff(c_1213,plain,(
    ! [C_278] :
      ( r2_hidden(k1_funct_1('#skF_5',C_278),k1_relat_1('#skF_6'))
      | k1_xboole_0 = '#skF_4'
      | ~ r2_hidden(C_278,'#skF_3')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_121,c_1211])).

tff(c_1219,plain,(
    ! [C_278] :
      ( r2_hidden(k1_funct_1('#skF_5',C_278),k1_relat_1('#skF_6'))
      | k1_xboole_0 = '#skF_4'
      | ~ r2_hidden(C_278,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_1213])).

tff(c_1221,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1219])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1233,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1221,c_8])).

tff(c_1236,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1233])).

tff(c_1239,plain,(
    ! [C_282] :
      ( r2_hidden(k1_funct_1('#skF_5',C_282),k1_relat_1('#skF_6'))
      | ~ r2_hidden(C_282,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_1219])).

tff(c_24,plain,(
    ! [A_20,B_21,C_23] :
      ( k7_partfun1(A_20,B_21,C_23) = k1_funct_1(B_21,C_23)
      | ~ r2_hidden(C_23,k1_relat_1(B_21))
      | ~ v1_funct_1(B_21)
      | ~ v5_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1241,plain,(
    ! [A_20,C_282] :
      ( k7_partfun1(A_20,'#skF_6',k1_funct_1('#skF_5',C_282)) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',C_282))
      | ~ v1_funct_1('#skF_6')
      | ~ v5_relat_1('#skF_6',A_20)
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden(C_282,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1239,c_24])).

tff(c_1278,plain,(
    ! [A_288,C_289] :
      ( k7_partfun1(A_288,'#skF_6',k1_funct_1('#skF_5',C_289)) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',C_289))
      | ~ v5_relat_1('#skF_6',A_288)
      | ~ r2_hidden(C_289,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_40,c_1241])).

tff(c_30,plain,(
    k7_partfun1('#skF_2','#skF_6',k1_funct_1('#skF_5','#skF_7')) != k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1284,plain,
    ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7'))
    | ~ v5_relat_1('#skF_6','#skF_2')
    | ~ r2_hidden('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1278,c_30])).

tff(c_1290,plain,
    ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7'))
    | ~ r2_hidden('#skF_7','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_1284])).

tff(c_1293,plain,(
    ~ r2_hidden('#skF_7','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1290])).

tff(c_1296,plain,
    ( v1_xboole_0('#skF_3')
    | ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_1293])).

tff(c_1299,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1296])).

tff(c_1301,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1258,c_1299])).

tff(c_1302,plain,(
    k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1290])).

tff(c_1309,plain,(
    ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1086,c_1302])).

tff(c_1313,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1309])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:56:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.89/1.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.89/1.64  
% 3.89/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.89/1.64  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.89/1.64  
% 3.89/1.64  %Foreground sorts:
% 3.89/1.64  
% 3.89/1.64  
% 3.89/1.64  %Background operators:
% 3.89/1.64  
% 3.89/1.64  
% 3.89/1.64  %Foreground operators:
% 3.89/1.64  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.89/1.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.89/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.89/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.89/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.89/1.64  tff('#skF_7', type, '#skF_7': $i).
% 3.89/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.89/1.64  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 3.89/1.64  tff('#skF_5', type, '#skF_5': $i).
% 3.89/1.64  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.89/1.64  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 3.89/1.64  tff('#skF_6', type, '#skF_6': $i).
% 3.89/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.89/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.89/1.64  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.89/1.64  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.89/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.89/1.64  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.89/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.89/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.89/1.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.89/1.64  tff('#skF_4', type, '#skF_4': $i).
% 3.89/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.89/1.64  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.89/1.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.89/1.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.89/1.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.89/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.89/1.64  
% 3.89/1.66  tff(f_134, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t186_funct_2)).
% 3.89/1.66  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.89/1.66  tff(f_97, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 3.89/1.66  tff(f_52, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.89/1.66  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.89/1.66  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.89/1.66  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.89/1.66  tff(f_73, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 3.89/1.66  tff(f_37, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.89/1.66  tff(f_109, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 3.89/1.66  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.89/1.66  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.89/1.66  tff(c_36, plain, (m1_subset_1('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.89/1.66  tff(c_32, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.89/1.66  tff(c_46, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.89/1.66  tff(c_44, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.89/1.66  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.89/1.66  tff(c_38, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.89/1.66  tff(c_108, plain, (![A_77, B_78, C_79]: (k1_relset_1(A_77, B_78, C_79)=k1_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.89/1.66  tff(c_116, plain, (k1_relset_1('#skF_4', '#skF_2', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_38, c_108])).
% 3.89/1.66  tff(c_34, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), k1_relset_1('#skF_4', '#skF_2', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.89/1.66  tff(c_121, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_34])).
% 3.89/1.66  tff(c_48, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.89/1.66  tff(c_40, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.89/1.66  tff(c_1047, plain, (![C_245, D_244, E_247, F_248, A_249, B_246]: (k1_funct_1(k8_funct_2(B_246, C_245, A_249, D_244, E_247), F_248)=k1_funct_1(E_247, k1_funct_1(D_244, F_248)) | k1_xboole_0=B_246 | ~r1_tarski(k2_relset_1(B_246, C_245, D_244), k1_relset_1(C_245, A_249, E_247)) | ~m1_subset_1(F_248, B_246) | ~m1_subset_1(E_247, k1_zfmisc_1(k2_zfmisc_1(C_245, A_249))) | ~v1_funct_1(E_247) | ~m1_subset_1(D_244, k1_zfmisc_1(k2_zfmisc_1(B_246, C_245))) | ~v1_funct_2(D_244, B_246, C_245) | ~v1_funct_1(D_244) | v1_xboole_0(C_245))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.89/1.66  tff(c_1049, plain, (![B_246, D_244, F_248]: (k1_funct_1(k8_funct_2(B_246, '#skF_4', '#skF_2', D_244, '#skF_6'), F_248)=k1_funct_1('#skF_6', k1_funct_1(D_244, F_248)) | k1_xboole_0=B_246 | ~r1_tarski(k2_relset_1(B_246, '#skF_4', D_244), k1_relat_1('#skF_6')) | ~m1_subset_1(F_248, B_246) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1(D_244, k1_zfmisc_1(k2_zfmisc_1(B_246, '#skF_4'))) | ~v1_funct_2(D_244, B_246, '#skF_4') | ~v1_funct_1(D_244) | v1_xboole_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_1047])).
% 3.89/1.66  tff(c_1053, plain, (![B_246, D_244, F_248]: (k1_funct_1(k8_funct_2(B_246, '#skF_4', '#skF_2', D_244, '#skF_6'), F_248)=k1_funct_1('#skF_6', k1_funct_1(D_244, F_248)) | k1_xboole_0=B_246 | ~r1_tarski(k2_relset_1(B_246, '#skF_4', D_244), k1_relat_1('#skF_6')) | ~m1_subset_1(F_248, B_246) | ~m1_subset_1(D_244, k1_zfmisc_1(k2_zfmisc_1(B_246, '#skF_4'))) | ~v1_funct_2(D_244, B_246, '#skF_4') | ~v1_funct_1(D_244) | v1_xboole_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_1049])).
% 3.89/1.66  tff(c_1080, plain, (![B_250, D_251, F_252]: (k1_funct_1(k8_funct_2(B_250, '#skF_4', '#skF_2', D_251, '#skF_6'), F_252)=k1_funct_1('#skF_6', k1_funct_1(D_251, F_252)) | k1_xboole_0=B_250 | ~r1_tarski(k2_relset_1(B_250, '#skF_4', D_251), k1_relat_1('#skF_6')) | ~m1_subset_1(F_252, B_250) | ~m1_subset_1(D_251, k1_zfmisc_1(k2_zfmisc_1(B_250, '#skF_4'))) | ~v1_funct_2(D_251, B_250, '#skF_4') | ~v1_funct_1(D_251))), inference(negUnitSimplification, [status(thm)], [c_48, c_1053])).
% 3.89/1.66  tff(c_1082, plain, (![F_252]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), F_252)=k1_funct_1('#skF_6', k1_funct_1('#skF_5', F_252)) | k1_xboole_0='#skF_3' | ~m1_subset_1(F_252, '#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_121, c_1080])).
% 3.89/1.66  tff(c_1085, plain, (![F_252]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), F_252)=k1_funct_1('#skF_6', k1_funct_1('#skF_5', F_252)) | k1_xboole_0='#skF_3' | ~m1_subset_1(F_252, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_1082])).
% 3.89/1.66  tff(c_1086, plain, (![F_252]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), F_252)=k1_funct_1('#skF_6', k1_funct_1('#skF_5', F_252)) | ~m1_subset_1(F_252, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_32, c_1085])).
% 3.89/1.66  tff(c_16, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.89/1.66  tff(c_56, plain, (![B_59, A_60]: (v1_relat_1(B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(A_60)) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.89/1.66  tff(c_59, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_42, c_56])).
% 3.89/1.66  tff(c_65, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_59])).
% 3.89/1.66  tff(c_99, plain, (![C_74, B_75, A_76]: (v5_relat_1(C_74, B_75) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_76, B_75))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.89/1.66  tff(c_106, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_99])).
% 3.89/1.66  tff(c_12, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.89/1.66  tff(c_150, plain, (![A_92, B_93, C_94]: (k7_partfun1(A_92, B_93, C_94)=k1_funct_1(B_93, C_94) | ~r2_hidden(C_94, k1_relat_1(B_93)) | ~v1_funct_1(B_93) | ~v5_relat_1(B_93, A_92) | ~v1_relat_1(B_93))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.89/1.66  tff(c_665, plain, (![A_184, B_185, A_186]: (k7_partfun1(A_184, B_185, A_186)=k1_funct_1(B_185, A_186) | ~v1_funct_1(B_185) | ~v5_relat_1(B_185, A_184) | ~v1_relat_1(B_185) | v1_xboole_0(k1_relat_1(B_185)) | ~m1_subset_1(A_186, k1_relat_1(B_185)))), inference(resolution, [status(thm)], [c_12, c_150])).
% 3.89/1.66  tff(c_669, plain, (![A_186]: (k7_partfun1('#skF_4', '#skF_5', A_186)=k1_funct_1('#skF_5', A_186) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | v1_xboole_0(k1_relat_1('#skF_5')) | ~m1_subset_1(A_186, k1_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_106, c_665])).
% 3.89/1.66  tff(c_675, plain, (![A_186]: (k7_partfun1('#skF_4', '#skF_5', A_186)=k1_funct_1('#skF_5', A_186) | v1_xboole_0(k1_relat_1('#skF_5')) | ~m1_subset_1(A_186, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_46, c_669])).
% 3.89/1.66  tff(c_1046, plain, (v1_xboole_0(k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_675])).
% 3.89/1.66  tff(c_10, plain, (![A_6]: (k1_xboole_0=A_6 | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.89/1.66  tff(c_1060, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_1046, c_10])).
% 3.89/1.66  tff(c_115, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_108])).
% 3.89/1.66  tff(c_1051, plain, (![B_246, D_244, F_248]: (k1_funct_1(k8_funct_2(B_246, '#skF_3', '#skF_4', D_244, '#skF_5'), F_248)=k1_funct_1('#skF_5', k1_funct_1(D_244, F_248)) | k1_xboole_0=B_246 | ~r1_tarski(k2_relset_1(B_246, '#skF_3', D_244), k1_relat_1('#skF_5')) | ~m1_subset_1(F_248, B_246) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_244, k1_zfmisc_1(k2_zfmisc_1(B_246, '#skF_3'))) | ~v1_funct_2(D_244, B_246, '#skF_3') | ~v1_funct_1(D_244) | v1_xboole_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_115, c_1047])).
% 3.89/1.66  tff(c_1056, plain, (![B_246, D_244, F_248]: (k1_funct_1(k8_funct_2(B_246, '#skF_3', '#skF_4', D_244, '#skF_5'), F_248)=k1_funct_1('#skF_5', k1_funct_1(D_244, F_248)) | k1_xboole_0=B_246 | ~r1_tarski(k2_relset_1(B_246, '#skF_3', D_244), k1_relat_1('#skF_5')) | ~m1_subset_1(F_248, B_246) | ~m1_subset_1(D_244, k1_zfmisc_1(k2_zfmisc_1(B_246, '#skF_3'))) | ~v1_funct_2(D_244, B_246, '#skF_3') | ~v1_funct_1(D_244) | v1_xboole_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_1051])).
% 3.89/1.66  tff(c_1248, plain, (![B_246, D_244, F_248]: (k1_funct_1(k8_funct_2(B_246, '#skF_3', '#skF_4', D_244, '#skF_5'), F_248)=k1_funct_1('#skF_5', k1_funct_1(D_244, F_248)) | k1_xboole_0=B_246 | ~r1_tarski(k2_relset_1(B_246, '#skF_3', D_244), k1_xboole_0) | ~m1_subset_1(F_248, B_246) | ~m1_subset_1(D_244, k1_zfmisc_1(k2_zfmisc_1(B_246, '#skF_3'))) | ~v1_funct_2(D_244, B_246, '#skF_3') | ~v1_funct_1(D_244) | v1_xboole_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1060, c_1056])).
% 3.89/1.66  tff(c_1249, plain, (v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_1248])).
% 3.89/1.66  tff(c_1252, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1249, c_10])).
% 3.89/1.66  tff(c_1256, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_1252])).
% 3.89/1.66  tff(c_1258, plain, (~v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_1248])).
% 3.89/1.66  tff(c_107, plain, (v5_relat_1('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_99])).
% 3.89/1.66  tff(c_62, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_56])).
% 3.89/1.66  tff(c_68, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_62])).
% 3.89/1.66  tff(c_638, plain, (![D_172, C_173, A_174, B_175]: (r2_hidden(k1_funct_1(D_172, C_173), k2_relset_1(A_174, B_175, D_172)) | k1_xboole_0=B_175 | ~r2_hidden(C_173, A_174) | ~m1_subset_1(D_172, k1_zfmisc_1(k2_zfmisc_1(A_174, B_175))) | ~v1_funct_2(D_172, A_174, B_175) | ~v1_funct_1(D_172))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.89/1.66  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.89/1.66  tff(c_1211, plain, (![A_279, B_281, B_280, C_278, D_277]: (r2_hidden(k1_funct_1(D_277, C_278), B_280) | ~r1_tarski(k2_relset_1(A_279, B_281, D_277), B_280) | k1_xboole_0=B_281 | ~r2_hidden(C_278, A_279) | ~m1_subset_1(D_277, k1_zfmisc_1(k2_zfmisc_1(A_279, B_281))) | ~v1_funct_2(D_277, A_279, B_281) | ~v1_funct_1(D_277))), inference(resolution, [status(thm)], [c_638, c_2])).
% 3.89/1.66  tff(c_1213, plain, (![C_278]: (r2_hidden(k1_funct_1('#skF_5', C_278), k1_relat_1('#skF_6')) | k1_xboole_0='#skF_4' | ~r2_hidden(C_278, '#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_121, c_1211])).
% 3.89/1.66  tff(c_1219, plain, (![C_278]: (r2_hidden(k1_funct_1('#skF_5', C_278), k1_relat_1('#skF_6')) | k1_xboole_0='#skF_4' | ~r2_hidden(C_278, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_1213])).
% 3.89/1.66  tff(c_1221, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_1219])).
% 3.89/1.66  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.89/1.66  tff(c_1233, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1221, c_8])).
% 3.89/1.66  tff(c_1236, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_1233])).
% 3.89/1.66  tff(c_1239, plain, (![C_282]: (r2_hidden(k1_funct_1('#skF_5', C_282), k1_relat_1('#skF_6')) | ~r2_hidden(C_282, '#skF_3'))), inference(splitRight, [status(thm)], [c_1219])).
% 3.89/1.66  tff(c_24, plain, (![A_20, B_21, C_23]: (k7_partfun1(A_20, B_21, C_23)=k1_funct_1(B_21, C_23) | ~r2_hidden(C_23, k1_relat_1(B_21)) | ~v1_funct_1(B_21) | ~v5_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.89/1.66  tff(c_1241, plain, (![A_20, C_282]: (k7_partfun1(A_20, '#skF_6', k1_funct_1('#skF_5', C_282))=k1_funct_1('#skF_6', k1_funct_1('#skF_5', C_282)) | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', A_20) | ~v1_relat_1('#skF_6') | ~r2_hidden(C_282, '#skF_3'))), inference(resolution, [status(thm)], [c_1239, c_24])).
% 3.89/1.66  tff(c_1278, plain, (![A_288, C_289]: (k7_partfun1(A_288, '#skF_6', k1_funct_1('#skF_5', C_289))=k1_funct_1('#skF_6', k1_funct_1('#skF_5', C_289)) | ~v5_relat_1('#skF_6', A_288) | ~r2_hidden(C_289, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_40, c_1241])).
% 3.89/1.66  tff(c_30, plain, (k7_partfun1('#skF_2', '#skF_6', k1_funct_1('#skF_5', '#skF_7'))!=k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.89/1.66  tff(c_1284, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7')) | ~v5_relat_1('#skF_6', '#skF_2') | ~r2_hidden('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1278, c_30])).
% 3.89/1.66  tff(c_1290, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7')) | ~r2_hidden('#skF_7', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_1284])).
% 3.89/1.66  tff(c_1293, plain, (~r2_hidden('#skF_7', '#skF_3')), inference(splitLeft, [status(thm)], [c_1290])).
% 3.89/1.66  tff(c_1296, plain, (v1_xboole_0('#skF_3') | ~m1_subset_1('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_12, c_1293])).
% 3.89/1.66  tff(c_1299, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1296])).
% 3.89/1.66  tff(c_1301, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1258, c_1299])).
% 3.89/1.66  tff(c_1302, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7'))), inference(splitRight, [status(thm)], [c_1290])).
% 3.89/1.66  tff(c_1309, plain, (~m1_subset_1('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1086, c_1302])).
% 3.89/1.66  tff(c_1313, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_1309])).
% 3.89/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.89/1.66  
% 3.89/1.66  Inference rules
% 3.89/1.66  ----------------------
% 3.89/1.66  #Ref     : 0
% 3.89/1.66  #Sup     : 258
% 3.89/1.66  #Fact    : 0
% 3.89/1.66  #Define  : 0
% 3.89/1.66  #Split   : 23
% 3.89/1.66  #Chain   : 0
% 3.89/1.66  #Close   : 0
% 3.89/1.66  
% 3.89/1.66  Ordering : KBO
% 3.89/1.66  
% 3.89/1.66  Simplification rules
% 3.89/1.66  ----------------------
% 3.89/1.66  #Subsume      : 49
% 3.89/1.66  #Demod        : 236
% 3.89/1.66  #Tautology    : 74
% 3.89/1.66  #SimpNegUnit  : 17
% 3.89/1.66  #BackRed      : 74
% 3.89/1.66  
% 3.89/1.66  #Partial instantiations: 0
% 3.89/1.66  #Strategies tried      : 1
% 3.89/1.66  
% 3.89/1.66  Timing (in seconds)
% 3.89/1.66  ----------------------
% 3.89/1.66  Preprocessing        : 0.33
% 3.89/1.66  Parsing              : 0.18
% 3.89/1.66  CNF conversion       : 0.03
% 3.89/1.66  Main loop            : 0.55
% 3.89/1.66  Inferencing          : 0.20
% 3.89/1.66  Reduction            : 0.17
% 3.89/1.66  Demodulation         : 0.11
% 3.89/1.66  BG Simplification    : 0.03
% 3.89/1.66  Subsumption          : 0.11
% 3.89/1.66  Abstraction          : 0.03
% 3.89/1.66  MUC search           : 0.00
% 3.89/1.66  Cooper               : 0.00
% 3.89/1.66  Total                : 0.92
% 3.89/1.66  Index Insertion      : 0.00
% 3.89/1.66  Index Deletion       : 0.00
% 3.89/1.66  Index Matching       : 0.00
% 3.89/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
