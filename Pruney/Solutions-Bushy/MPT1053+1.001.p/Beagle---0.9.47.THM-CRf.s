%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1053+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:20 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 681 expanded)
%              Number of leaves         :   32 ( 263 expanded)
%              Depth                    :   18
%              Number of atoms          :  234 (1719 expanded)
%              Number of equality atoms :   34 ( 398 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > k11_relat_1 > #nlpp > k9_setfam_1 > k2_subset_1 > k1_zfmisc_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_94,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,k9_setfam_1(A))
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,k9_setfam_1(A)))) )
       => ? [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A)))
            & ! [D] :
                ( r2_hidden(D,A)
               => k11_relat_1(C,D) = k1_funct_1(B,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t170_funct_2)).

tff(f_32,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_27,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_26,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,k9_setfam_1(A))
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,k9_setfam_1(A)))) )
     => ( ! [C] :
            ( m1_subset_1(C,A)
           => ( r2_hidden(C,k2_subset_1(A))
             => r1_tarski(k1_funct_1(B,C),k2_subset_1(A)) ) )
       => ? [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(A),k2_subset_1(A))))
            & ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,k2_subset_1(A))
                 => k11_relat_1(C,D) = k1_funct_1(B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_relset_1__e2_192__funct_2)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_30,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(c_36,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_8,plain,(
    ! [A_3] : k9_setfam_1(A_3) = k1_zfmisc_1(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_34,plain,(
    v1_funct_2('#skF_4','#skF_3',k9_setfam_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_41,plain,(
    v1_funct_2('#skF_4','#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_34])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k9_setfam_1('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_zfmisc_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_32])).

tff(c_4,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_65,plain,(
    ! [A_28] :
      ( k1_xboole_0 = A_28
      | ~ v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_69,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_65])).

tff(c_79,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_4])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_18,plain,(
    ! [A_4,B_5] :
      ( r2_hidden('#skF_1'(A_4,B_5),k2_subset_1(A_4))
      | m1_subset_1('#skF_2'(A_4,B_5),k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(A_4),k2_subset_1(A_4))))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(k2_zfmisc_1(A_4,k9_setfam_1(A_4))))
      | ~ v1_funct_2(B_5,A_4,k9_setfam_1(A_4))
      | ~ v1_funct_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_44,plain,(
    ! [A_4,B_5] :
      ( r2_hidden('#skF_1'(A_4,B_5),k2_subset_1(A_4))
      | m1_subset_1('#skF_2'(A_4,B_5),k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(A_4),k2_subset_1(A_4))))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(k2_zfmisc_1(A_4,k1_zfmisc_1(A_4))))
      | ~ v1_funct_2(B_5,A_4,k1_zfmisc_1(A_4))
      | ~ v1_funct_1(B_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_18])).

tff(c_164,plain,(
    ! [A_53,B_54] :
      ( r2_hidden('#skF_1'(A_53,B_54),A_53)
      | m1_subset_1('#skF_2'(A_53,B_54),k1_zfmisc_1(k2_zfmisc_1(A_53,A_53)))
      | ~ m1_subset_1(B_54,k1_zfmisc_1(k2_zfmisc_1(A_53,k1_zfmisc_1(A_53))))
      | ~ v1_funct_2(B_54,A_53,k1_zfmisc_1(A_53))
      | ~ v1_funct_1(B_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_2,c_44])).

tff(c_40,plain,(
    ! [C_24] :
      ( r2_hidden('#skF_5'(C_24),'#skF_3')
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_189,plain,(
    ! [B_57] :
      ( r2_hidden('#skF_5'('#skF_2'('#skF_3',B_57)),'#skF_3')
      | r2_hidden('#skF_1'('#skF_3',B_57),'#skF_3')
      | ~ m1_subset_1(B_57,k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_zfmisc_1('#skF_3'))))
      | ~ v1_funct_2(B_57,'#skF_3',k1_zfmisc_1('#skF_3'))
      | ~ v1_funct_1(B_57) ) ),
    inference(resolution,[status(thm)],[c_164,c_40])).

tff(c_196,plain,
    ( r2_hidden('#skF_5'('#skF_2'('#skF_3','#skF_4')),'#skF_3')
    | r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_3',k1_zfmisc_1('#skF_3'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_189])).

tff(c_204,plain,
    ( r2_hidden('#skF_5'('#skF_2'('#skF_3','#skF_4')),'#skF_3')
    | r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_41,c_196])).

tff(c_231,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_204])).

tff(c_30,plain,(
    ! [D_20,C_19,B_18,A_17] :
      ( r2_hidden(k1_funct_1(D_20,C_19),B_18)
      | k1_xboole_0 = B_18
      | ~ r2_hidden(C_19,A_17)
      | ~ m1_subset_1(D_20,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18)))
      | ~ v1_funct_2(D_20,A_17,B_18)
      | ~ v1_funct_1(D_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_240,plain,(
    ! [D_58,B_59] :
      ( r2_hidden(k1_funct_1(D_58,'#skF_1'('#skF_3','#skF_4')),B_59)
      | k1_xboole_0 = B_59
      | ~ m1_subset_1(D_58,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_59)))
      | ~ v1_funct_2(D_58,'#skF_3',B_59)
      | ~ v1_funct_1(D_58) ) ),
    inference(resolution,[status(thm)],[c_231,c_30])).

tff(c_22,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,B_13)
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_249,plain,(
    ! [D_62,B_63] :
      ( m1_subset_1(k1_funct_1(D_62,'#skF_1'('#skF_3','#skF_4')),B_63)
      | k1_xboole_0 = B_63
      | ~ m1_subset_1(D_62,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_63)))
      | ~ v1_funct_2(D_62,'#skF_3',B_63)
      | ~ v1_funct_1(D_62) ) ),
    inference(resolution,[status(thm)],[c_240,c_22])).

tff(c_24,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_303,plain,(
    ! [D_67,B_68] :
      ( r1_tarski(k1_funct_1(D_67,'#skF_1'('#skF_3','#skF_4')),B_68)
      | k1_zfmisc_1(B_68) = k1_xboole_0
      | ~ m1_subset_1(D_67,k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_zfmisc_1(B_68))))
      | ~ v1_funct_2(D_67,'#skF_3',k1_zfmisc_1(B_68))
      | ~ v1_funct_1(D_67) ) ),
    inference(resolution,[status(thm)],[c_249,c_24])).

tff(c_314,plain,
    ( r1_tarski(k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_4')),'#skF_3')
    | k1_zfmisc_1('#skF_3') = k1_xboole_0
    | ~ v1_funct_2('#skF_4','#skF_3',k1_zfmisc_1('#skF_3'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_303])).

tff(c_323,plain,
    ( r1_tarski(k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_4')),'#skF_3')
    | k1_zfmisc_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_41,c_314])).

tff(c_325,plain,(
    k1_zfmisc_1('#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_323])).

tff(c_6,plain,(
    ! [A_2] : ~ v1_xboole_0(k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_346,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_6])).

tff(c_352,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_346])).

tff(c_353,plain,(
    r1_tarski(k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_4')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_323])).

tff(c_16,plain,(
    ! [B_5,A_4] :
      ( ~ r1_tarski(k1_funct_1(B_5,'#skF_1'(A_4,B_5)),k2_subset_1(A_4))
      | m1_subset_1('#skF_2'(A_4,B_5),k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(A_4),k2_subset_1(A_4))))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(k2_zfmisc_1(A_4,k9_setfam_1(A_4))))
      | ~ v1_funct_2(B_5,A_4,k9_setfam_1(A_4))
      | ~ v1_funct_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_45,plain,(
    ! [B_5,A_4] :
      ( ~ r1_tarski(k1_funct_1(B_5,'#skF_1'(A_4,B_5)),k2_subset_1(A_4))
      | m1_subset_1('#skF_2'(A_4,B_5),k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(A_4),k2_subset_1(A_4))))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(k2_zfmisc_1(A_4,k1_zfmisc_1(A_4))))
      | ~ v1_funct_2(B_5,A_4,k1_zfmisc_1(A_4))
      | ~ v1_funct_1(B_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_16])).

tff(c_51,plain,(
    ! [B_5,A_4] :
      ( ~ r1_tarski(k1_funct_1(B_5,'#skF_1'(A_4,B_5)),A_4)
      | m1_subset_1('#skF_2'(A_4,B_5),k1_zfmisc_1(k2_zfmisc_1(A_4,A_4)))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(k2_zfmisc_1(A_4,k1_zfmisc_1(A_4))))
      | ~ v1_funct_2(B_5,A_4,k1_zfmisc_1(A_4))
      | ~ v1_funct_1(B_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_2,c_45])).

tff(c_356,plain,
    ( m1_subset_1('#skF_2'('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_zfmisc_1('#skF_3'))))
    | ~ v1_funct_2('#skF_4','#skF_3',k1_zfmisc_1('#skF_3'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_353,c_51])).

tff(c_359,plain,(
    m1_subset_1('#skF_2'('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_41,c_42,c_356])).

tff(c_385,plain,(
    r2_hidden('#skF_5'('#skF_2'('#skF_3','#skF_4')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_359,c_40])).

tff(c_392,plain,(
    m1_subset_1('#skF_5'('#skF_2'('#skF_3','#skF_4')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_385,c_22])).

tff(c_354,plain,(
    k1_zfmisc_1('#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_323])).

tff(c_105,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_3',k1_zfmisc_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_42,c_24])).

tff(c_26,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_324,plain,(
    ! [A_14,B_68] :
      ( r1_tarski(k1_funct_1(A_14,'#skF_1'('#skF_3','#skF_4')),B_68)
      | k1_zfmisc_1(B_68) = k1_xboole_0
      | ~ v1_funct_2(A_14,'#skF_3',k1_zfmisc_1(B_68))
      | ~ v1_funct_1(A_14)
      | ~ r1_tarski(A_14,k2_zfmisc_1('#skF_3',k1_zfmisc_1(B_68))) ) ),
    inference(resolution,[status(thm)],[c_26,c_303])).

tff(c_10,plain,(
    ! [B_5,A_4,D_11] :
      ( ~ r1_tarski(k1_funct_1(B_5,'#skF_1'(A_4,B_5)),k2_subset_1(A_4))
      | k11_relat_1('#skF_2'(A_4,B_5),D_11) = k1_funct_1(B_5,D_11)
      | ~ r2_hidden(D_11,k2_subset_1(A_4))
      | ~ m1_subset_1(D_11,A_4)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(k2_zfmisc_1(A_4,k9_setfam_1(A_4))))
      | ~ v1_funct_2(B_5,A_4,k9_setfam_1(A_4))
      | ~ v1_funct_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_48,plain,(
    ! [B_5,A_4,D_11] :
      ( ~ r1_tarski(k1_funct_1(B_5,'#skF_1'(A_4,B_5)),k2_subset_1(A_4))
      | k11_relat_1('#skF_2'(A_4,B_5),D_11) = k1_funct_1(B_5,D_11)
      | ~ r2_hidden(D_11,k2_subset_1(A_4))
      | ~ m1_subset_1(D_11,A_4)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(k2_zfmisc_1(A_4,k1_zfmisc_1(A_4))))
      | ~ v1_funct_2(B_5,A_4,k1_zfmisc_1(A_4))
      | ~ v1_funct_1(B_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_10])).

tff(c_592,plain,(
    ! [B_95,A_96,D_97] :
      ( ~ r1_tarski(k1_funct_1(B_95,'#skF_1'(A_96,B_95)),A_96)
      | k11_relat_1('#skF_2'(A_96,B_95),D_97) = k1_funct_1(B_95,D_97)
      | ~ r2_hidden(D_97,A_96)
      | ~ m1_subset_1(D_97,A_96)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(k2_zfmisc_1(A_96,k1_zfmisc_1(A_96))))
      | ~ v1_funct_2(B_95,A_96,k1_zfmisc_1(A_96))
      | ~ v1_funct_1(B_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_48])).

tff(c_595,plain,(
    ! [D_97] :
      ( k11_relat_1('#skF_2'('#skF_3','#skF_4'),D_97) = k1_funct_1('#skF_4',D_97)
      | ~ r2_hidden(D_97,'#skF_3')
      | ~ m1_subset_1(D_97,'#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_zfmisc_1('#skF_3'))))
      | k1_zfmisc_1('#skF_3') = k1_xboole_0
      | ~ v1_funct_2('#skF_4','#skF_3',k1_zfmisc_1('#skF_3'))
      | ~ v1_funct_1('#skF_4')
      | ~ r1_tarski('#skF_4',k2_zfmisc_1('#skF_3',k1_zfmisc_1('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_324,c_592])).

tff(c_600,plain,(
    ! [D_97] :
      ( k11_relat_1('#skF_2'('#skF_3','#skF_4'),D_97) = k1_funct_1('#skF_4',D_97)
      | ~ r2_hidden(D_97,'#skF_3')
      | ~ m1_subset_1(D_97,'#skF_3')
      | k1_zfmisc_1('#skF_3') = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_36,c_41,c_42,c_595])).

tff(c_605,plain,(
    ! [D_98] :
      ( k11_relat_1('#skF_2'('#skF_3','#skF_4'),D_98) = k1_funct_1('#skF_4',D_98)
      | ~ r2_hidden(D_98,'#skF_3')
      | ~ m1_subset_1(D_98,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_354,c_600])).

tff(c_38,plain,(
    ! [C_24] :
      ( k1_funct_1('#skF_4','#skF_5'(C_24)) != k11_relat_1(C_24,'#skF_5'(C_24))
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_611,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ r2_hidden('#skF_5'('#skF_2'('#skF_3','#skF_4')),'#skF_3')
    | ~ m1_subset_1('#skF_5'('#skF_2'('#skF_3','#skF_4')),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_605,c_38])).

tff(c_619,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_385,c_359,c_611])).

tff(c_621,plain,(
    ~ r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_204])).

tff(c_50,plain,(
    ! [A_4,B_5] :
      ( r2_hidden('#skF_1'(A_4,B_5),A_4)
      | m1_subset_1('#skF_2'(A_4,B_5),k1_zfmisc_1(k2_zfmisc_1(A_4,A_4)))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(k2_zfmisc_1(A_4,k1_zfmisc_1(A_4))))
      | ~ v1_funct_2(B_5,A_4,k1_zfmisc_1(A_4))
      | ~ v1_funct_1(B_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_2,c_44])).

tff(c_620,plain,(
    r2_hidden('#skF_5'('#skF_2'('#skF_3','#skF_4')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_204])).

tff(c_628,plain,(
    m1_subset_1('#skF_5'('#skF_2'('#skF_3','#skF_4')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_620,c_22])).

tff(c_12,plain,(
    ! [A_4,B_5,D_11] :
      ( r2_hidden('#skF_1'(A_4,B_5),k2_subset_1(A_4))
      | k11_relat_1('#skF_2'(A_4,B_5),D_11) = k1_funct_1(B_5,D_11)
      | ~ r2_hidden(D_11,k2_subset_1(A_4))
      | ~ m1_subset_1(D_11,A_4)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(k2_zfmisc_1(A_4,k9_setfam_1(A_4))))
      | ~ v1_funct_2(B_5,A_4,k9_setfam_1(A_4))
      | ~ v1_funct_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_47,plain,(
    ! [A_4,B_5,D_11] :
      ( r2_hidden('#skF_1'(A_4,B_5),k2_subset_1(A_4))
      | k11_relat_1('#skF_2'(A_4,B_5),D_11) = k1_funct_1(B_5,D_11)
      | ~ r2_hidden(D_11,k2_subset_1(A_4))
      | ~ m1_subset_1(D_11,A_4)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(k2_zfmisc_1(A_4,k1_zfmisc_1(A_4))))
      | ~ v1_funct_2(B_5,A_4,k1_zfmisc_1(A_4))
      | ~ v1_funct_1(B_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_12])).

tff(c_881,plain,(
    ! [A_135,B_136,D_137] :
      ( r2_hidden('#skF_1'(A_135,B_136),A_135)
      | k11_relat_1('#skF_2'(A_135,B_136),D_137) = k1_funct_1(B_136,D_137)
      | ~ r2_hidden(D_137,A_135)
      | ~ m1_subset_1(D_137,A_135)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(k2_zfmisc_1(A_135,k1_zfmisc_1(A_135))))
      | ~ v1_funct_2(B_136,A_135,k1_zfmisc_1(A_135))
      | ~ v1_funct_1(B_136) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_47])).

tff(c_889,plain,(
    ! [D_137] :
      ( r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_3')
      | k11_relat_1('#skF_2'('#skF_3','#skF_4'),D_137) = k1_funct_1('#skF_4',D_137)
      | ~ r2_hidden(D_137,'#skF_3')
      | ~ m1_subset_1(D_137,'#skF_3')
      | ~ v1_funct_2('#skF_4','#skF_3',k1_zfmisc_1('#skF_3'))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_881])).

tff(c_897,plain,(
    ! [D_137] :
      ( r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_3')
      | k11_relat_1('#skF_2'('#skF_3','#skF_4'),D_137) = k1_funct_1('#skF_4',D_137)
      | ~ r2_hidden(D_137,'#skF_3')
      | ~ m1_subset_1(D_137,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_41,c_889])).

tff(c_900,plain,(
    ! [D_138] :
      ( k11_relat_1('#skF_2'('#skF_3','#skF_4'),D_138) = k1_funct_1('#skF_4',D_138)
      | ~ r2_hidden(D_138,'#skF_3')
      | ~ m1_subset_1(D_138,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_621,c_897])).

tff(c_906,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ r2_hidden('#skF_5'('#skF_2'('#skF_3','#skF_4')),'#skF_3')
    | ~ m1_subset_1('#skF_5'('#skF_2'('#skF_3','#skF_4')),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_900,c_38])).

tff(c_913,plain,(
    ~ m1_subset_1('#skF_2'('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_628,c_620,c_906])).

tff(c_917,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_zfmisc_1('#skF_3'))))
    | ~ v1_funct_2('#skF_4','#skF_3',k1_zfmisc_1('#skF_3'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_913])).

tff(c_926,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_41,c_42,c_917])).

tff(c_928,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_621,c_926])).

%------------------------------------------------------------------------------
