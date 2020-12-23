%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:57 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 213 expanded)
%              Number of leaves         :   25 (  87 expanded)
%              Depth                    :   12
%              Number of atoms          :  153 ( 698 expanded)
%              Number of equality atoms :   24 (  56 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,A)
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,A,B)
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
                   => r2_hidden(k3_funct_2(A,B,D,C),k2_relset_1(A,B,D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_funct_2)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => m1_subset_1(k3_funct_2(A,B,C,D),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_funct_2)).

tff(c_28,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_30,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_26,plain,(
    m1_subset_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,B_6)
      | v1_xboole_0(B_6)
      | ~ m1_subset_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_24,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_22,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_20,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_16,plain,(
    ! [D_18,C_17,A_15,B_16] :
      ( r2_hidden(k1_funct_1(D_18,C_17),k2_relset_1(A_15,B_16,D_18))
      | k1_xboole_0 = B_16
      | ~ r2_hidden(C_17,A_15)
      | ~ m1_subset_1(D_18,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16)))
      | ~ v1_funct_2(D_18,A_15,B_16)
      | ~ v1_funct_1(D_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_256,plain,(
    ! [A_76,B_77,C_78,D_79] :
      ( k3_funct_2(A_76,B_77,C_78,D_79) = k1_funct_1(C_78,D_79)
      | ~ m1_subset_1(D_79,A_76)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77)))
      | ~ v1_funct_2(C_78,A_76,B_77)
      | ~ v1_funct_1(C_78)
      | v1_xboole_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_264,plain,(
    ! [B_77,C_78] :
      ( k3_funct_2('#skF_1',B_77,C_78,'#skF_3') = k1_funct_1(C_78,'#skF_3')
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_77)))
      | ~ v1_funct_2(C_78,'#skF_1',B_77)
      | ~ v1_funct_1(C_78)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_256])).

tff(c_274,plain,(
    ! [B_80,C_81] :
      ( k3_funct_2('#skF_1',B_80,C_81,'#skF_3') = k1_funct_1(C_81,'#skF_3')
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_80)))
      | ~ v1_funct_2(C_81,'#skF_1',B_80)
      | ~ v1_funct_1(C_81) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_264])).

tff(c_277,plain,
    ( k3_funct_2('#skF_1','#skF_2','#skF_4','#skF_3') = k1_funct_1('#skF_4','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_274])).

tff(c_284,plain,(
    k3_funct_2('#skF_1','#skF_2','#skF_4','#skF_3') = k1_funct_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_277])).

tff(c_18,plain,(
    ~ r2_hidden(k3_funct_2('#skF_1','#skF_2','#skF_4','#skF_3'),k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_286,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_3'),k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_18])).

tff(c_304,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r2_hidden('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_286])).

tff(c_310,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r2_hidden('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_304])).

tff(c_312,plain,(
    ~ r2_hidden('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_310])).

tff(c_315,plain,
    ( v1_xboole_0('#skF_1')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_312])).

tff(c_318,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_315])).

tff(c_320,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_318])).

tff(c_321,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_310])).

tff(c_183,plain,(
    ! [D_59,C_60,A_61,B_62] :
      ( r2_hidden(k1_funct_1(D_59,C_60),k2_relset_1(A_61,B_62,D_59))
      | k1_xboole_0 = B_62
      | ~ r2_hidden(C_60,A_61)
      | ~ m1_subset_1(D_59,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62)))
      | ~ v1_funct_2(D_59,A_61,B_62)
      | ~ v1_funct_1(D_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_131,plain,(
    ! [A_51,B_52,C_53,D_54] :
      ( k3_funct_2(A_51,B_52,C_53,D_54) = k1_funct_1(C_53,D_54)
      | ~ m1_subset_1(D_54,A_51)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52)))
      | ~ v1_funct_2(C_53,A_51,B_52)
      | ~ v1_funct_1(C_53)
      | v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_137,plain,(
    ! [B_52,C_53] :
      ( k3_funct_2('#skF_1',B_52,C_53,'#skF_3') = k1_funct_1(C_53,'#skF_3')
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_52)))
      | ~ v1_funct_2(C_53,'#skF_1',B_52)
      | ~ v1_funct_1(C_53)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_131])).

tff(c_148,plain,(
    ! [B_57,C_58] :
      ( k3_funct_2('#skF_1',B_57,C_58,'#skF_3') = k1_funct_1(C_58,'#skF_3')
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_57)))
      | ~ v1_funct_2(C_58,'#skF_1',B_57)
      | ~ v1_funct_1(C_58) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_137])).

tff(c_151,plain,
    ( k3_funct_2('#skF_1','#skF_2','#skF_4','#skF_3') = k1_funct_1('#skF_4','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_148])).

tff(c_158,plain,(
    k3_funct_2('#skF_1','#skF_2','#skF_4','#skF_3') = k1_funct_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_151])).

tff(c_160,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_3'),k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_18])).

tff(c_186,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r2_hidden('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_183,c_160])).

tff(c_189,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r2_hidden('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_186])).

tff(c_190,plain,(
    ~ r2_hidden('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_189])).

tff(c_193,plain,
    ( v1_xboole_0('#skF_1')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_190])).

tff(c_196,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_193])).

tff(c_198,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_196])).

tff(c_199,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_189])).

tff(c_72,plain,(
    ! [A_37,B_38] :
      ( r2_hidden(A_37,B_38)
      | v1_xboole_0(B_38)
      | ~ m1_subset_1(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_53,plain,(
    ! [A_32,B_33] : ~ r2_hidden(A_32,k2_zfmisc_1(A_32,B_33)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_56,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_53])).

tff(c_81,plain,(
    ! [A_37] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1(A_37,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_72,c_56])).

tff(c_83,plain,(
    ! [A_37] : ~ m1_subset_1(A_37,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_206,plain,(
    ! [A_37] : ~ m1_subset_1(A_37,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_83])).

tff(c_99,plain,(
    ! [A_42,B_43,C_44,D_45] :
      ( m1_subset_1(k3_funct_2(A_42,B_43,C_44,D_45),B_43)
      | ~ m1_subset_1(D_45,A_42)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43)))
      | ~ v1_funct_2(C_44,A_42,B_43)
      | ~ v1_funct_1(C_44)
      | v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_101,plain,(
    ! [D_45] :
      ( m1_subset_1(k3_funct_2('#skF_1','#skF_2','#skF_4',D_45),'#skF_2')
      | ~ m1_subset_1(D_45,'#skF_1')
      | ~ v1_funct_2('#skF_4','#skF_1','#skF_2')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_20,c_99])).

tff(c_108,plain,(
    ! [D_45] :
      ( m1_subset_1(k3_funct_2('#skF_1','#skF_2','#skF_4',D_45),'#skF_2')
      | ~ m1_subset_1(D_45,'#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_101])).

tff(c_109,plain,(
    ! [D_45] :
      ( m1_subset_1(k3_funct_2('#skF_1','#skF_2','#skF_4',D_45),'#skF_2')
      | ~ m1_subset_1(D_45,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_108])).

tff(c_164,plain,
    ( m1_subset_1(k1_funct_1('#skF_4','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_109])).

tff(c_168,plain,(
    m1_subset_1(k1_funct_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_164])).

tff(c_226,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_206,c_168])).

tff(c_227,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_330,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_227])).

tff(c_336,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_330])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:35:56 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.42/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.32  
% 2.42/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.32  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.42/1.32  
% 2.42/1.32  %Foreground sorts:
% 2.42/1.32  
% 2.42/1.32  
% 2.42/1.32  %Background operators:
% 2.42/1.32  
% 2.42/1.32  
% 2.42/1.32  %Foreground operators:
% 2.42/1.32  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.42/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.42/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.42/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.42/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.42/1.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.42/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.42/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.42/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.42/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.42/1.32  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.42/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.42/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.42/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.42/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.42/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.42/1.32  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.42/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.42/1.32  
% 2.42/1.34  tff(f_98, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, A) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_hidden(k3_funct_2(A, B, D, C), k2_relset_1(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t189_funct_2)).
% 2.42/1.34  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.42/1.34  tff(f_78, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 2.42/1.34  tff(f_66, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.42/1.34  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.42/1.34  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.42/1.34  tff(f_53, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => m1_subset_1(k3_funct_2(A, B, C, D), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_funct_2)).
% 2.42/1.34  tff(c_28, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.42/1.34  tff(c_30, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.42/1.34  tff(c_26, plain, (m1_subset_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.42/1.34  tff(c_10, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | v1_xboole_0(B_6) | ~m1_subset_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.42/1.34  tff(c_24, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.42/1.34  tff(c_22, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.42/1.34  tff(c_20, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.42/1.34  tff(c_16, plain, (![D_18, C_17, A_15, B_16]: (r2_hidden(k1_funct_1(D_18, C_17), k2_relset_1(A_15, B_16, D_18)) | k1_xboole_0=B_16 | ~r2_hidden(C_17, A_15) | ~m1_subset_1(D_18, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))) | ~v1_funct_2(D_18, A_15, B_16) | ~v1_funct_1(D_18))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.42/1.34  tff(c_256, plain, (![A_76, B_77, C_78, D_79]: (k3_funct_2(A_76, B_77, C_78, D_79)=k1_funct_1(C_78, D_79) | ~m1_subset_1(D_79, A_76) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))) | ~v1_funct_2(C_78, A_76, B_77) | ~v1_funct_1(C_78) | v1_xboole_0(A_76))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.42/1.34  tff(c_264, plain, (![B_77, C_78]: (k3_funct_2('#skF_1', B_77, C_78, '#skF_3')=k1_funct_1(C_78, '#skF_3') | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_77))) | ~v1_funct_2(C_78, '#skF_1', B_77) | ~v1_funct_1(C_78) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_256])).
% 2.42/1.34  tff(c_274, plain, (![B_80, C_81]: (k3_funct_2('#skF_1', B_80, C_81, '#skF_3')=k1_funct_1(C_81, '#skF_3') | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_80))) | ~v1_funct_2(C_81, '#skF_1', B_80) | ~v1_funct_1(C_81))), inference(negUnitSimplification, [status(thm)], [c_30, c_264])).
% 2.42/1.34  tff(c_277, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_4', '#skF_3')=k1_funct_1('#skF_4', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_274])).
% 2.42/1.34  tff(c_284, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_4', '#skF_3')=k1_funct_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_277])).
% 2.42/1.34  tff(c_18, plain, (~r2_hidden(k3_funct_2('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.42/1.34  tff(c_286, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_3'), k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_284, c_18])).
% 2.42/1.34  tff(c_304, plain, (k1_xboole_0='#skF_2' | ~r2_hidden('#skF_3', '#skF_1') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_286])).
% 2.42/1.34  tff(c_310, plain, (k1_xboole_0='#skF_2' | ~r2_hidden('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_304])).
% 2.42/1.34  tff(c_312, plain, (~r2_hidden('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_310])).
% 2.42/1.34  tff(c_315, plain, (v1_xboole_0('#skF_1') | ~m1_subset_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_10, c_312])).
% 2.42/1.34  tff(c_318, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_315])).
% 2.42/1.34  tff(c_320, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_318])).
% 2.42/1.34  tff(c_321, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_310])).
% 2.42/1.34  tff(c_183, plain, (![D_59, C_60, A_61, B_62]: (r2_hidden(k1_funct_1(D_59, C_60), k2_relset_1(A_61, B_62, D_59)) | k1_xboole_0=B_62 | ~r2_hidden(C_60, A_61) | ~m1_subset_1(D_59, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))) | ~v1_funct_2(D_59, A_61, B_62) | ~v1_funct_1(D_59))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.42/1.34  tff(c_131, plain, (![A_51, B_52, C_53, D_54]: (k3_funct_2(A_51, B_52, C_53, D_54)=k1_funct_1(C_53, D_54) | ~m1_subset_1(D_54, A_51) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))) | ~v1_funct_2(C_53, A_51, B_52) | ~v1_funct_1(C_53) | v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.42/1.34  tff(c_137, plain, (![B_52, C_53]: (k3_funct_2('#skF_1', B_52, C_53, '#skF_3')=k1_funct_1(C_53, '#skF_3') | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_52))) | ~v1_funct_2(C_53, '#skF_1', B_52) | ~v1_funct_1(C_53) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_131])).
% 2.42/1.34  tff(c_148, plain, (![B_57, C_58]: (k3_funct_2('#skF_1', B_57, C_58, '#skF_3')=k1_funct_1(C_58, '#skF_3') | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_57))) | ~v1_funct_2(C_58, '#skF_1', B_57) | ~v1_funct_1(C_58))), inference(negUnitSimplification, [status(thm)], [c_30, c_137])).
% 2.42/1.34  tff(c_151, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_4', '#skF_3')=k1_funct_1('#skF_4', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_148])).
% 2.42/1.34  tff(c_158, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_4', '#skF_3')=k1_funct_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_151])).
% 2.42/1.34  tff(c_160, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_3'), k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_18])).
% 2.42/1.34  tff(c_186, plain, (k1_xboole_0='#skF_2' | ~r2_hidden('#skF_3', '#skF_1') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_183, c_160])).
% 2.42/1.34  tff(c_189, plain, (k1_xboole_0='#skF_2' | ~r2_hidden('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_186])).
% 2.42/1.34  tff(c_190, plain, (~r2_hidden('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_189])).
% 2.42/1.34  tff(c_193, plain, (v1_xboole_0('#skF_1') | ~m1_subset_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_10, c_190])).
% 2.42/1.34  tff(c_196, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_193])).
% 2.42/1.34  tff(c_198, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_196])).
% 2.42/1.34  tff(c_199, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_189])).
% 2.42/1.34  tff(c_72, plain, (![A_37, B_38]: (r2_hidden(A_37, B_38) | v1_xboole_0(B_38) | ~m1_subset_1(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.42/1.34  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.42/1.34  tff(c_53, plain, (![A_32, B_33]: (~r2_hidden(A_32, k2_zfmisc_1(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.42/1.34  tff(c_56, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_53])).
% 2.42/1.34  tff(c_81, plain, (![A_37]: (v1_xboole_0(k1_xboole_0) | ~m1_subset_1(A_37, k1_xboole_0))), inference(resolution, [status(thm)], [c_72, c_56])).
% 2.42/1.34  tff(c_83, plain, (![A_37]: (~m1_subset_1(A_37, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_81])).
% 2.42/1.34  tff(c_206, plain, (![A_37]: (~m1_subset_1(A_37, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_199, c_83])).
% 2.42/1.34  tff(c_99, plain, (![A_42, B_43, C_44, D_45]: (m1_subset_1(k3_funct_2(A_42, B_43, C_44, D_45), B_43) | ~m1_subset_1(D_45, A_42) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))) | ~v1_funct_2(C_44, A_42, B_43) | ~v1_funct_1(C_44) | v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.42/1.34  tff(c_101, plain, (![D_45]: (m1_subset_1(k3_funct_2('#skF_1', '#skF_2', '#skF_4', D_45), '#skF_2') | ~m1_subset_1(D_45, '#skF_1') | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_99])).
% 2.42/1.34  tff(c_108, plain, (![D_45]: (m1_subset_1(k3_funct_2('#skF_1', '#skF_2', '#skF_4', D_45), '#skF_2') | ~m1_subset_1(D_45, '#skF_1') | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_101])).
% 2.42/1.34  tff(c_109, plain, (![D_45]: (m1_subset_1(k3_funct_2('#skF_1', '#skF_2', '#skF_4', D_45), '#skF_2') | ~m1_subset_1(D_45, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_30, c_108])).
% 2.42/1.34  tff(c_164, plain, (m1_subset_1(k1_funct_1('#skF_4', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_158, c_109])).
% 2.42/1.34  tff(c_168, plain, (m1_subset_1(k1_funct_1('#skF_4', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_164])).
% 2.42/1.34  tff(c_226, plain, $false, inference(negUnitSimplification, [status(thm)], [c_206, c_168])).
% 2.42/1.34  tff(c_227, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_81])).
% 2.42/1.34  tff(c_330, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_321, c_227])).
% 2.42/1.34  tff(c_336, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_330])).
% 2.42/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.34  
% 2.42/1.34  Inference rules
% 2.42/1.34  ----------------------
% 2.42/1.34  #Ref     : 0
% 2.42/1.34  #Sup     : 57
% 2.42/1.34  #Fact    : 0
% 2.42/1.34  #Define  : 0
% 2.42/1.34  #Split   : 7
% 2.42/1.34  #Chain   : 0
% 2.42/1.34  #Close   : 0
% 2.42/1.34  
% 2.42/1.34  Ordering : KBO
% 2.42/1.34  
% 2.42/1.34  Simplification rules
% 2.42/1.34  ----------------------
% 2.42/1.34  #Subsume      : 8
% 2.42/1.34  #Demod        : 63
% 2.42/1.34  #Tautology    : 18
% 2.42/1.34  #SimpNegUnit  : 19
% 2.42/1.34  #BackRed      : 24
% 2.42/1.34  
% 2.42/1.34  #Partial instantiations: 0
% 2.42/1.34  #Strategies tried      : 1
% 2.42/1.34  
% 2.42/1.34  Timing (in seconds)
% 2.42/1.34  ----------------------
% 2.42/1.35  Preprocessing        : 0.33
% 2.42/1.35  Parsing              : 0.18
% 2.42/1.35  CNF conversion       : 0.02
% 2.42/1.35  Main loop            : 0.24
% 2.42/1.35  Inferencing          : 0.08
% 2.42/1.35  Reduction            : 0.08
% 2.42/1.35  Demodulation         : 0.05
% 2.42/1.35  BG Simplification    : 0.01
% 2.42/1.35  Subsumption          : 0.04
% 2.42/1.35  Abstraction          : 0.02
% 2.42/1.35  MUC search           : 0.00
% 2.42/1.35  Cooper               : 0.00
% 2.42/1.35  Total                : 0.60
% 2.42/1.35  Index Insertion      : 0.00
% 2.42/1.35  Index Deletion       : 0.00
% 2.42/1.35  Index Matching       : 0.00
% 2.42/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
