%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:29 EST 2020

% Result     : Theorem 9.67s
% Output     : CNFRefutation 9.78s
% Verified   : 
% Statistics : Number of formulae       :  255 (2980 expanded)
%              Number of leaves         :   36 (1024 expanded)
%              Depth                    :   19
%              Number of atoms          :  480 (8217 expanded)
%              Number of equality atoms :  136 (2265 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_47,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_117,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ~ ( r2_hidden(F,A)
                    & r2_hidden(F,C)
                    & E = k1_funct_1(D,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_98,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_12,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_68,plain,(
    ! [B_49,A_50] :
      ( v1_relat_1(B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_50))
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_74,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_50,c_68])).

tff(c_78,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_74])).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_159,plain,(
    ! [A_77,B_78,C_79,D_80] :
      ( k7_relset_1(A_77,B_78,C_79,D_80) = k9_relat_1(C_79,D_80)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_166,plain,(
    ! [D_80] : k7_relset_1('#skF_2','#skF_3','#skF_5',D_80) = k9_relat_1('#skF_5',D_80) ),
    inference(resolution,[status(thm)],[c_50,c_159])).

tff(c_48,plain,(
    r2_hidden('#skF_6',k7_relset_1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_169,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_48])).

tff(c_16,plain,(
    ! [A_13,B_14,C_15] :
      ( r2_hidden('#skF_1'(A_13,B_14,C_15),B_14)
      | ~ r2_hidden(A_13,k9_relat_1(C_15,B_14))
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4108,plain,(
    ! [A_683,B_684,C_685] :
      ( r2_hidden(k4_tarski('#skF_1'(A_683,B_684,C_685),A_683),C_685)
      | ~ r2_hidden(A_683,k9_relat_1(C_685,B_684))
      | ~ v1_relat_1(C_685) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_24,plain,(
    ! [C_21,A_19,B_20] :
      ( k1_funct_1(C_21,A_19) = B_20
      | ~ r2_hidden(k4_tarski(A_19,B_20),C_21)
      | ~ v1_funct_1(C_21)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4439,plain,(
    ! [C_743,A_744,B_745] :
      ( k1_funct_1(C_743,'#skF_1'(A_744,B_745,C_743)) = A_744
      | ~ v1_funct_1(C_743)
      | ~ r2_hidden(A_744,k9_relat_1(C_743,B_745))
      | ~ v1_relat_1(C_743) ) ),
    inference(resolution,[status(thm)],[c_4108,c_24])).

tff(c_4456,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_169,c_4439])).

tff(c_4467,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_54,c_4456])).

tff(c_52,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_108,plain,(
    ! [A_58,B_59,C_60] :
      ( k1_relset_1(A_58,B_59,C_60) = k1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_117,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_108])).

tff(c_4491,plain,(
    ! [B_746,A_747,C_748] :
      ( k1_xboole_0 = B_746
      | k1_relset_1(A_747,B_746,C_748) = A_747
      | ~ v1_funct_2(C_748,A_747,B_746)
      | ~ m1_subset_1(C_748,k1_zfmisc_1(k2_zfmisc_1(A_747,B_746))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4510,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_4491])).

tff(c_4519,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_117,c_4510])).

tff(c_4520,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4519])).

tff(c_20,plain,(
    ! [A_13,B_14,C_15] :
      ( r2_hidden('#skF_1'(A_13,B_14,C_15),k1_relat_1(C_15))
      | ~ r2_hidden(A_13,k9_relat_1(C_15,B_14))
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_22,plain,(
    ! [A_19,C_21] :
      ( r2_hidden(k4_tarski(A_19,k1_funct_1(C_21,A_19)),C_21)
      | ~ r2_hidden(A_19,k1_relat_1(C_21))
      | ~ v1_funct_1(C_21)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4472,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4467,c_22])).

tff(c_4476,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_54,c_4472])).

tff(c_4478,plain,(
    ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_4476])).

tff(c_4481,plain,
    ( ~ r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_4478])).

tff(c_4485,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_169,c_4481])).

tff(c_4487,plain,(
    r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_4476])).

tff(c_4521,plain,(
    r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4520,c_4487])).

tff(c_46,plain,(
    ! [F_40] :
      ( k1_funct_1('#skF_5',F_40) != '#skF_6'
      | ~ r2_hidden(F_40,'#skF_4')
      | ~ r2_hidden(F_40,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_4541,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6'
    | ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_4521,c_46])).

tff(c_4545,plain,(
    ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4467,c_4541])).

tff(c_4548,plain,
    ( ~ r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_4545])).

tff(c_4552,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_169,c_4548])).

tff(c_4553,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4519])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4590,plain,(
    ! [A_1] : r1_tarski('#skF_3',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4553,c_2])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_189,plain,(
    ! [A_84,B_85,A_86,D_87] :
      ( k7_relset_1(A_84,B_85,A_86,D_87) = k9_relat_1(A_86,D_87)
      | ~ r1_tarski(A_86,k2_zfmisc_1(A_84,B_85)) ) ),
    inference(resolution,[status(thm)],[c_8,c_159])).

tff(c_2791,plain,(
    ! [A_476,B_477,D_478] : k7_relset_1(A_476,B_477,k1_xboole_0,D_478) = k9_relat_1(k1_xboole_0,D_478) ),
    inference(resolution,[status(thm)],[c_2,c_189])).

tff(c_28,plain,(
    ! [A_22,B_23,C_24,D_25] :
      ( m1_subset_1(k7_relset_1(A_22,B_23,C_24,D_25),k1_zfmisc_1(B_23))
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3869,plain,(
    ! [D_638,B_639,A_640] :
      ( m1_subset_1(k9_relat_1(k1_xboole_0,D_638),k1_zfmisc_1(B_639))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_640,B_639))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2791,c_28])).

tff(c_3872,plain,(
    ! [D_638,B_639,A_640] :
      ( m1_subset_1(k9_relat_1(k1_xboole_0,D_638),k1_zfmisc_1(B_639))
      | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(A_640,B_639)) ) ),
    inference(resolution,[status(thm)],[c_8,c_3869])).

tff(c_3877,plain,(
    ! [D_641,B_642] : m1_subset_1(k9_relat_1(k1_xboole_0,D_641),k1_zfmisc_1(B_642)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_3872])).

tff(c_198,plain,(
    ! [A_88,B_89,C_90,D_91] :
      ( m1_subset_1(k7_relset_1(A_88,B_89,C_90,D_91),k1_zfmisc_1(B_89))
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_214,plain,(
    ! [D_80] :
      ( m1_subset_1(k9_relat_1('#skF_5',D_80),k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_198])).

tff(c_221,plain,(
    ! [D_92] : m1_subset_1(k9_relat_1('#skF_5',D_92),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_214])).

tff(c_97,plain,(
    ! [C_53,A_54,B_55] :
      ( r2_hidden(C_53,A_54)
      | ~ r2_hidden(C_53,B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_100,plain,(
    ! [A_54] :
      ( r2_hidden('#skF_6',A_54)
      | ~ m1_subset_1(k7_relset_1('#skF_2','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1(A_54)) ) ),
    inference(resolution,[status(thm)],[c_48,c_97])).

tff(c_168,plain,(
    ! [A_54] :
      ( r2_hidden('#skF_6',A_54)
      | ~ m1_subset_1(k9_relat_1('#skF_5','#skF_4'),k1_zfmisc_1(A_54)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_100])).

tff(c_232,plain,(
    r2_hidden('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_221,c_168])).

tff(c_4,plain,(
    ! [C_5,A_2,B_3] :
      ( r2_hidden(C_5,A_2)
      | ~ r2_hidden(C_5,B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1017,plain,(
    ! [A_219] :
      ( r2_hidden('#skF_6',A_219)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_219)) ) ),
    inference(resolution,[status(thm)],[c_232,c_4])).

tff(c_1023,plain,(
    ! [B_220] :
      ( r2_hidden('#skF_6',B_220)
      | ~ r1_tarski('#skF_3',B_220) ) ),
    inference(resolution,[status(thm)],[c_8,c_1017])).

tff(c_1030,plain,(
    ! [A_2,B_220] :
      ( r2_hidden('#skF_6',A_2)
      | ~ m1_subset_1(B_220,k1_zfmisc_1(A_2))
      | ~ r1_tarski('#skF_3',B_220) ) ),
    inference(resolution,[status(thm)],[c_1023,c_4])).

tff(c_3907,plain,(
    ! [B_642,D_641] :
      ( r2_hidden('#skF_6',B_642)
      | ~ r1_tarski('#skF_3',k9_relat_1(k1_xboole_0,D_641)) ) ),
    inference(resolution,[status(thm)],[c_3877,c_1030])).

tff(c_3957,plain,(
    ! [D_641] : ~ r1_tarski('#skF_3',k9_relat_1(k1_xboole_0,D_641)) ),
    inference(splitLeft,[status(thm)],[c_3907])).

tff(c_4580,plain,(
    ! [D_641] : ~ r1_tarski('#skF_3',k9_relat_1('#skF_3',D_641)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4553,c_3957])).

tff(c_4737,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4590,c_4580])).

tff(c_4738,plain,(
    ! [B_642] : r2_hidden('#skF_6',B_642) ),
    inference(splitRight,[status(thm)],[c_3907])).

tff(c_5833,plain,(
    ! [A_926,B_927,C_928] :
      ( r2_hidden(k4_tarski('#skF_1'(A_926,B_927,C_928),A_926),C_928)
      | ~ r2_hidden(A_926,k9_relat_1(C_928,B_927))
      | ~ v1_relat_1(C_928) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6018,plain,(
    ! [C_957,A_958,B_959] :
      ( k1_funct_1(C_957,'#skF_1'(A_958,B_959,C_957)) = A_958
      | ~ v1_funct_1(C_957)
      | ~ r2_hidden(A_958,k9_relat_1(C_957,B_959))
      | ~ v1_relat_1(C_957) ) ),
    inference(resolution,[status(thm)],[c_5833,c_24])).

tff(c_6033,plain,(
    ! [C_957,B_959] :
      ( k1_funct_1(C_957,'#skF_1'('#skF_6',B_959,C_957)) = '#skF_6'
      | ~ v1_funct_1(C_957)
      | ~ v1_relat_1(C_957) ) ),
    inference(resolution,[status(thm)],[c_4738,c_6018])).

tff(c_6347,plain,(
    ! [B_1006,A_1007,C_1008] :
      ( k1_xboole_0 = B_1006
      | k1_relset_1(A_1007,B_1006,C_1008) = A_1007
      | ~ v1_funct_2(C_1008,A_1007,B_1006)
      | ~ m1_subset_1(C_1008,k1_zfmisc_1(k2_zfmisc_1(A_1007,B_1006))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_6370,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_6347])).

tff(c_6380,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_117,c_6370])).

tff(c_6381,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_6380])).

tff(c_6386,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_1'(A_13,B_14,'#skF_5'),'#skF_2')
      | ~ r2_hidden(A_13,k9_relat_1('#skF_5',B_14))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6381,c_20])).

tff(c_6396,plain,(
    ! [A_1009,B_1010] :
      ( r2_hidden('#skF_1'(A_1009,B_1010,'#skF_5'),'#skF_2')
      | ~ r2_hidden(A_1009,k9_relat_1('#skF_5',B_1010)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_6386])).

tff(c_6522,plain,(
    ! [A_1029,B_1030] :
      ( k1_funct_1('#skF_5','#skF_1'(A_1029,B_1030,'#skF_5')) != '#skF_6'
      | ~ r2_hidden('#skF_1'(A_1029,B_1030,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_1029,k9_relat_1('#skF_5',B_1030)) ) ),
    inference(resolution,[status(thm)],[c_6396,c_46])).

tff(c_6530,plain,(
    ! [A_13] :
      ( k1_funct_1('#skF_5','#skF_1'(A_13,'#skF_4','#skF_5')) != '#skF_6'
      | ~ r2_hidden(A_13,k9_relat_1('#skF_5','#skF_4'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_16,c_6522])).

tff(c_6545,plain,(
    ! [A_1033] :
      ( k1_funct_1('#skF_5','#skF_1'(A_1033,'#skF_4','#skF_5')) != '#skF_6'
      | ~ r2_hidden(A_1033,k9_relat_1('#skF_5','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_6530])).

tff(c_6587,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6' ),
    inference(resolution,[status(thm)],[c_4738,c_6545])).

tff(c_6591,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6033,c_6587])).

tff(c_6595,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_54,c_6591])).

tff(c_6596,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_6380])).

tff(c_6635,plain,(
    ! [A_1] : r1_tarski('#skF_3',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6596,c_2])).

tff(c_58,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,B_47)
      | ~ m1_subset_1(A_46,k1_zfmisc_1(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_66,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_50,c_58])).

tff(c_3814,plain,(
    ! [C_627,A_628] :
      ( k1_xboole_0 = C_627
      | ~ v1_funct_2(C_627,A_628,k1_xboole_0)
      | k1_xboole_0 = A_628
      | ~ m1_subset_1(C_627,k1_zfmisc_1(k2_zfmisc_1(A_628,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3824,plain,(
    ! [A_6,A_628] :
      ( k1_xboole_0 = A_6
      | ~ v1_funct_2(A_6,A_628,k1_xboole_0)
      | k1_xboole_0 = A_628
      | ~ r1_tarski(A_6,k2_zfmisc_1(A_628,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_8,c_3814])).

tff(c_6720,plain,(
    ! [A_1047,A_1048] :
      ( A_1047 = '#skF_3'
      | ~ v1_funct_2(A_1047,A_1048,'#skF_3')
      | A_1048 = '#skF_3'
      | ~ r1_tarski(A_1047,k2_zfmisc_1(A_1048,'#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6596,c_6596,c_6596,c_6596,c_3824])).

tff(c_6735,plain,
    ( '#skF_5' = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_66,c_6720])).

tff(c_6742,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_6735])).

tff(c_6743,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_6742])).

tff(c_6597,plain,(
    k1_relat_1('#skF_5') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_6380])).

tff(c_6744,plain,(
    k1_relat_1('#skF_5') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6743,c_6597])).

tff(c_6754,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6743,c_52])).

tff(c_6750,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6743,c_117])).

tff(c_6752,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6743,c_66])).

tff(c_4769,plain,(
    ! [B_764,C_765] :
      ( k1_relset_1(k1_xboole_0,B_764,C_765) = k1_xboole_0
      | ~ v1_funct_2(C_765,k1_xboole_0,B_764)
      | ~ m1_subset_1(C_765,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_764))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4784,plain,(
    ! [B_764,A_6] :
      ( k1_relset_1(k1_xboole_0,B_764,A_6) = k1_xboole_0
      | ~ v1_funct_2(A_6,k1_xboole_0,B_764)
      | ~ r1_tarski(A_6,k2_zfmisc_1(k1_xboole_0,B_764)) ) ),
    inference(resolution,[status(thm)],[c_8,c_4769])).

tff(c_6959,plain,(
    ! [B_1064,A_1065] :
      ( k1_relset_1('#skF_3',B_1064,A_1065) = '#skF_3'
      | ~ v1_funct_2(A_1065,'#skF_3',B_1064)
      | ~ r1_tarski(A_1065,k2_zfmisc_1('#skF_3',B_1064)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6596,c_6596,c_6596,c_6596,c_4784])).

tff(c_6966,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_6752,c_6959])).

tff(c_6982,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6754,c_6750,c_6966])).

tff(c_6984,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6744,c_6982])).

tff(c_6985,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_6742])).

tff(c_3408,plain,(
    ! [B_583,A_584,C_585] :
      ( k1_xboole_0 = B_583
      | k1_relset_1(A_584,B_583,C_585) = A_584
      | ~ v1_funct_2(C_585,A_584,B_583)
      | ~ m1_subset_1(C_585,k1_zfmisc_1(k2_zfmisc_1(A_584,B_583))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3427,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_3408])).

tff(c_3435,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_117,c_3427])).

tff(c_3436,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_3435])).

tff(c_3441,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_1'(A_13,B_14,'#skF_5'),'#skF_2')
      | ~ r2_hidden(A_13,k9_relat_1('#skF_5',B_14))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3436,c_20])).

tff(c_3451,plain,(
    ! [A_586,B_587] :
      ( r2_hidden('#skF_1'(A_586,B_587,'#skF_5'),'#skF_2')
      | ~ r2_hidden(A_586,k9_relat_1('#skF_5',B_587)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_3441])).

tff(c_3612,plain,(
    ! [A_612,B_613] :
      ( k1_funct_1('#skF_5','#skF_1'(A_612,B_613,'#skF_5')) != '#skF_6'
      | ~ r2_hidden('#skF_1'(A_612,B_613,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_612,k9_relat_1('#skF_5',B_613)) ) ),
    inference(resolution,[status(thm)],[c_3451,c_46])).

tff(c_3620,plain,(
    ! [A_13] :
      ( k1_funct_1('#skF_5','#skF_1'(A_13,'#skF_4','#skF_5')) != '#skF_6'
      | ~ r2_hidden(A_13,k9_relat_1('#skF_5','#skF_4'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_16,c_3612])).

tff(c_3625,plain,(
    ! [A_614] :
      ( k1_funct_1('#skF_5','#skF_1'(A_614,'#skF_4','#skF_5')) != '#skF_6'
      | ~ r2_hidden(A_614,k9_relat_1('#skF_5','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_3620])).

tff(c_3662,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6' ),
    inference(resolution,[status(thm)],[c_169,c_3625])).

tff(c_2905,plain,(
    ! [A_495,B_496,C_497] :
      ( r2_hidden(k4_tarski('#skF_1'(A_495,B_496,C_497),A_495),C_497)
      | ~ r2_hidden(A_495,k9_relat_1(C_497,B_496))
      | ~ v1_relat_1(C_497) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_3664,plain,(
    ! [C_615,A_616,B_617] :
      ( k1_funct_1(C_615,'#skF_1'(A_616,B_617,C_615)) = A_616
      | ~ v1_funct_1(C_615)
      | ~ r2_hidden(A_616,k9_relat_1(C_615,B_617))
      | ~ v1_relat_1(C_615) ) ),
    inference(resolution,[status(thm)],[c_2905,c_24])).

tff(c_3681,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_169,c_3664])).

tff(c_3692,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_54,c_3681])).

tff(c_3694,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3662,c_3692])).

tff(c_3695,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3435])).

tff(c_3754,plain,(
    ! [A_1] : r1_tarski('#skF_3',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3695,c_2])).

tff(c_2803,plain,(
    ! [A_479,B_480] :
      ( r2_hidden('#skF_6',A_479)
      | ~ m1_subset_1(B_480,k1_zfmisc_1(A_479))
      | ~ r1_tarski('#skF_3',B_480) ) ),
    inference(resolution,[status(thm)],[c_1023,c_4])).

tff(c_2820,plain,
    ( r2_hidden('#skF_6',k2_zfmisc_1('#skF_2','#skF_3'))
    | ~ r1_tarski('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_2803])).

tff(c_2821,plain,(
    ~ r1_tarski('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2820])).

tff(c_3771,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3754,c_2821])).

tff(c_3773,plain,(
    r1_tarski('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_2820])).

tff(c_3783,plain,(
    ! [B_622,A_623] :
      ( r2_hidden('#skF_6',B_622)
      | ~ r1_tarski('#skF_3',A_623)
      | ~ r1_tarski(A_623,B_622) ) ),
    inference(resolution,[status(thm)],[c_8,c_2803])).

tff(c_3790,plain,(
    ! [B_624] :
      ( r2_hidden('#skF_6',B_624)
      | ~ r1_tarski('#skF_5',B_624) ) ),
    inference(resolution,[status(thm)],[c_3773,c_3783])).

tff(c_3797,plain,(
    ! [A_2,B_624] :
      ( r2_hidden('#skF_6',A_2)
      | ~ m1_subset_1(B_624,k1_zfmisc_1(A_2))
      | ~ r1_tarski('#skF_5',B_624) ) ),
    inference(resolution,[status(thm)],[c_3790,c_4])).

tff(c_3904,plain,(
    ! [B_642,D_641] :
      ( r2_hidden('#skF_6',B_642)
      | ~ r1_tarski('#skF_5',k9_relat_1(k1_xboole_0,D_641)) ) ),
    inference(resolution,[status(thm)],[c_3877,c_3797])).

tff(c_3955,plain,(
    ! [D_641] : ~ r1_tarski('#skF_5',k9_relat_1(k1_xboole_0,D_641)) ),
    inference(splitLeft,[status(thm)],[c_3904])).

tff(c_6626,plain,(
    ! [D_641] : ~ r1_tarski('#skF_5',k9_relat_1('#skF_3',D_641)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6596,c_3955])).

tff(c_6987,plain,(
    ! [D_641] : ~ r1_tarski('#skF_3',k9_relat_1('#skF_3',D_641)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6985,c_6626])).

tff(c_7005,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6635,c_6987])).

tff(c_7006,plain,(
    ! [B_642] : r2_hidden('#skF_6',B_642) ),
    inference(splitRight,[status(thm)],[c_3904])).

tff(c_12297,plain,(
    ! [A_1746,B_1747,C_1748] :
      ( r2_hidden(k4_tarski('#skF_1'(A_1746,B_1747,C_1748),A_1746),C_1748)
      | ~ r2_hidden(A_1746,k9_relat_1(C_1748,B_1747))
      | ~ v1_relat_1(C_1748) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_12600,plain,(
    ! [C_1801,A_1802,B_1803] :
      ( k1_funct_1(C_1801,'#skF_1'(A_1802,B_1803,C_1801)) = A_1802
      | ~ v1_funct_1(C_1801)
      | ~ r2_hidden(A_1802,k9_relat_1(C_1801,B_1803))
      | ~ v1_relat_1(C_1801) ) ),
    inference(resolution,[status(thm)],[c_12297,c_24])).

tff(c_12615,plain,(
    ! [C_1801,B_1803] :
      ( k1_funct_1(C_1801,'#skF_1'('#skF_6',B_1803,C_1801)) = '#skF_6'
      | ~ v1_funct_1(C_1801)
      | ~ v1_relat_1(C_1801) ) ),
    inference(resolution,[status(thm)],[c_7006,c_12600])).

tff(c_12629,plain,(
    ! [B_1806,A_1807,C_1808] :
      ( k1_xboole_0 = B_1806
      | k1_relset_1(A_1807,B_1806,C_1808) = A_1807
      | ~ v1_funct_2(C_1808,A_1807,B_1806)
      | ~ m1_subset_1(C_1808,k1_zfmisc_1(k2_zfmisc_1(A_1807,B_1806))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_12648,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_12629])).

tff(c_12657,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_117,c_12648])).

tff(c_12658,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_12657])).

tff(c_12663,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_1'(A_13,B_14,'#skF_5'),'#skF_2')
      | ~ r2_hidden(A_13,k9_relat_1('#skF_5',B_14))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12658,c_20])).

tff(c_12673,plain,(
    ! [A_1809,B_1810] :
      ( r2_hidden('#skF_1'(A_1809,B_1810,'#skF_5'),'#skF_2')
      | ~ r2_hidden(A_1809,k9_relat_1('#skF_5',B_1810)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_12663])).

tff(c_12798,plain,(
    ! [A_1828,B_1829] :
      ( k1_funct_1('#skF_5','#skF_1'(A_1828,B_1829,'#skF_5')) != '#skF_6'
      | ~ r2_hidden('#skF_1'(A_1828,B_1829,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_1828,k9_relat_1('#skF_5',B_1829)) ) ),
    inference(resolution,[status(thm)],[c_12673,c_46])).

tff(c_12806,plain,(
    ! [A_13] :
      ( k1_funct_1('#skF_5','#skF_1'(A_13,'#skF_4','#skF_5')) != '#skF_6'
      | ~ r2_hidden(A_13,k9_relat_1('#skF_5','#skF_4'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_16,c_12798])).

tff(c_12811,plain,(
    ! [A_1830] :
      ( k1_funct_1('#skF_5','#skF_1'(A_1830,'#skF_4','#skF_5')) != '#skF_6'
      | ~ r2_hidden(A_1830,k9_relat_1('#skF_5','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_12806])).

tff(c_12839,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6' ),
    inference(resolution,[status(thm)],[c_7006,c_12811])).

tff(c_12843,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_12615,c_12839])).

tff(c_12847,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_54,c_12843])).

tff(c_12848,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_12657])).

tff(c_3875,plain,(
    ! [D_638,B_639] : m1_subset_1(k9_relat_1(k1_xboole_0,D_638),k1_zfmisc_1(B_639)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_3872])).

tff(c_32,plain,(
    ! [A_29,B_30,C_31,D_32] :
      ( k7_relset_1(A_29,B_30,C_31,D_32) = k9_relat_1(C_31,D_32)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_7049,plain,(
    ! [A_1072,B_1073,D_1074,D_1075] : k7_relset_1(A_1072,B_1073,k9_relat_1(k1_xboole_0,D_1074),D_1075) = k9_relat_1(k9_relat_1(k1_xboole_0,D_1074),D_1075) ),
    inference(resolution,[status(thm)],[c_3877,c_32])).

tff(c_7055,plain,(
    ! [D_1074,D_1075,B_1073,A_1072] :
      ( m1_subset_1(k9_relat_1(k9_relat_1(k1_xboole_0,D_1074),D_1075),k1_zfmisc_1(B_1073))
      | ~ m1_subset_1(k9_relat_1(k1_xboole_0,D_1074),k1_zfmisc_1(k2_zfmisc_1(A_1072,B_1073))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7049,c_28])).

tff(c_7061,plain,(
    ! [D_1074,D_1075,B_1073] : m1_subset_1(k9_relat_1(k9_relat_1(k1_xboole_0,D_1074),D_1075),k1_zfmisc_1(B_1073)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3875,c_7055])).

tff(c_12866,plain,(
    ! [D_1074,D_1075,B_1073] : m1_subset_1(k9_relat_1(k9_relat_1('#skF_3',D_1074),D_1075),k1_zfmisc_1(B_1073)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12848,c_7061])).

tff(c_7063,plain,(
    ! [D_1076,D_1077,B_1078] : m1_subset_1(k9_relat_1(k9_relat_1(k1_xboole_0,D_1076),D_1077),k1_zfmisc_1(B_1078)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3875,c_7055])).

tff(c_7082,plain,(
    ! [A_29,D_1077,D_1076,D_32,B_30] : k7_relset_1(A_29,B_30,k9_relat_1(k9_relat_1(k1_xboole_0,D_1076),D_1077),D_32) = k9_relat_1(k9_relat_1(k9_relat_1(k1_xboole_0,D_1076),D_1077),D_32) ),
    inference(resolution,[status(thm)],[c_7063,c_32])).

tff(c_14028,plain,(
    ! [B_1991,D_1993,D_1990,D_1989,A_1992] : k7_relset_1(A_1992,B_1991,k9_relat_1(k9_relat_1('#skF_3',D_1990),D_1993),D_1989) = k9_relat_1(k9_relat_1(k9_relat_1('#skF_3',D_1990),D_1993),D_1989) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12848,c_12848,c_7082])).

tff(c_14037,plain,(
    ! [B_1991,D_1993,D_1990,D_1989,A_1992] :
      ( m1_subset_1(k9_relat_1(k9_relat_1(k9_relat_1('#skF_3',D_1990),D_1993),D_1989),k1_zfmisc_1(B_1991))
      | ~ m1_subset_1(k9_relat_1(k9_relat_1('#skF_3',D_1990),D_1993),k1_zfmisc_1(k2_zfmisc_1(A_1992,B_1991))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14028,c_28])).

tff(c_14045,plain,(
    ! [D_1990,D_1993,D_1989,B_1991] : m1_subset_1(k9_relat_1(k9_relat_1(k9_relat_1('#skF_3',D_1990),D_1993),D_1989),k1_zfmisc_1(B_1991)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12866,c_14037])).

tff(c_14025,plain,(
    ! [A_29,D_1077,D_1076,D_32,B_30] : k7_relset_1(A_29,B_30,k9_relat_1(k9_relat_1('#skF_3',D_1076),D_1077),D_32) = k9_relat_1(k9_relat_1(k9_relat_1('#skF_3',D_1076),D_1077),D_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12848,c_12848,c_7082])).

tff(c_14848,plain,(
    ! [D_2101,B_2102,A_2104,A_2103,C_2105,D_2100] :
      ( k7_relset_1(A_2103,B_2102,k7_relset_1(A_2104,k2_zfmisc_1(A_2103,B_2102),C_2105,D_2101),D_2100) = k9_relat_1(k7_relset_1(A_2104,k2_zfmisc_1(A_2103,B_2102),C_2105,D_2101),D_2100)
      | ~ m1_subset_1(C_2105,k1_zfmisc_1(k2_zfmisc_1(A_2104,k2_zfmisc_1(A_2103,B_2102)))) ) ),
    inference(resolution,[status(thm)],[c_198,c_32])).

tff(c_14854,plain,(
    ! [D_2101,D_1074,D_1075,B_2102,A_2104,A_2103,D_2100] : k7_relset_1(A_2103,B_2102,k7_relset_1(A_2104,k2_zfmisc_1(A_2103,B_2102),k9_relat_1(k9_relat_1('#skF_3',D_1074),D_1075),D_2101),D_2100) = k9_relat_1(k7_relset_1(A_2104,k2_zfmisc_1(A_2103,B_2102),k9_relat_1(k9_relat_1('#skF_3',D_1074),D_1075),D_2101),D_2100) ),
    inference(resolution,[status(thm)],[c_12866,c_14848])).

tff(c_15587,plain,(
    ! [A_2197,D_2194,B_2192,D_2195,D_2196,D_2193] : k7_relset_1(A_2197,B_2192,k9_relat_1(k9_relat_1(k9_relat_1('#skF_3',D_2193),D_2195),D_2194),D_2196) = k9_relat_1(k9_relat_1(k9_relat_1(k9_relat_1('#skF_3',D_2193),D_2195),D_2194),D_2196) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14025,c_14025,c_14854])).

tff(c_15602,plain,(
    ! [A_2197,D_2194,B_2192,D_2195,D_2196,D_2193] :
      ( m1_subset_1(k9_relat_1(k9_relat_1(k9_relat_1(k9_relat_1('#skF_3',D_2193),D_2195),D_2194),D_2196),k1_zfmisc_1(B_2192))
      | ~ m1_subset_1(k9_relat_1(k9_relat_1(k9_relat_1('#skF_3',D_2193),D_2195),D_2194),k1_zfmisc_1(k2_zfmisc_1(A_2197,B_2192))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15587,c_28])).

tff(c_15614,plain,(
    ! [D_2194,B_2192,D_2195,D_2196,D_2193] : m1_subset_1(k9_relat_1(k9_relat_1(k9_relat_1(k9_relat_1('#skF_3',D_2193),D_2195),D_2194),D_2196),k1_zfmisc_1(B_2192)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14045,c_15602])).

tff(c_10,plain,(
    ! [B_10,A_8] :
      ( v1_relat_1(B_10)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_8))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_233,plain,(
    ! [D_92] :
      ( v1_relat_1(k9_relat_1('#skF_5',D_92))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_221,c_10])).

tff(c_250,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_233])).

tff(c_572,plain,(
    ! [A_159,B_160,C_161] :
      ( r2_hidden(k4_tarski('#skF_1'(A_159,B_160,C_161),A_159),C_161)
      | ~ r2_hidden(A_159,k9_relat_1(C_161,B_160))
      | ~ v1_relat_1(C_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_893,plain,(
    ! [C_209,A_210,B_211] :
      ( k1_funct_1(C_209,'#skF_1'(A_210,B_211,C_209)) = A_210
      | ~ v1_funct_1(C_209)
      | ~ r2_hidden(A_210,k9_relat_1(C_209,B_211))
      | ~ v1_relat_1(C_209) ) ),
    inference(resolution,[status(thm)],[c_572,c_24])).

tff(c_907,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_169,c_893])).

tff(c_917,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_54,c_907])).

tff(c_736,plain,(
    ! [B_183,A_184,C_185] :
      ( k1_xboole_0 = B_183
      | k1_relset_1(A_184,B_183,C_185) = A_184
      | ~ v1_funct_2(C_185,A_184,B_183)
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(A_184,B_183))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_755,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_736])).

tff(c_763,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_117,c_755])).

tff(c_771,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_763])).

tff(c_776,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_1'(A_13,B_14,'#skF_5'),'#skF_2')
      | ~ r2_hidden(A_13,k9_relat_1('#skF_5',B_14))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_771,c_20])).

tff(c_786,plain,(
    ! [A_187,B_188] :
      ( r2_hidden('#skF_1'(A_187,B_188,'#skF_5'),'#skF_2')
      | ~ r2_hidden(A_187,k9_relat_1('#skF_5',B_188)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_776])).

tff(c_919,plain,(
    ! [A_212,B_213] :
      ( k1_funct_1('#skF_5','#skF_1'(A_212,B_213,'#skF_5')) != '#skF_6'
      | ~ r2_hidden('#skF_1'(A_212,B_213,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_212,k9_relat_1('#skF_5',B_213)) ) ),
    inference(resolution,[status(thm)],[c_786,c_46])).

tff(c_927,plain,(
    ! [A_13] :
      ( k1_funct_1('#skF_5','#skF_1'(A_13,'#skF_4','#skF_5')) != '#skF_6'
      | ~ r2_hidden(A_13,k9_relat_1('#skF_5','#skF_4'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_16,c_919])).

tff(c_941,plain,(
    ! [A_214] :
      ( k1_funct_1('#skF_5','#skF_1'(A_214,'#skF_4','#skF_5')) != '#skF_6'
      | ~ r2_hidden(A_214,k9_relat_1('#skF_5','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_927])).

tff(c_960,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6' ),
    inference(resolution,[status(thm)],[c_169,c_941])).

tff(c_974,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_917,c_960])).

tff(c_975,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_763])).

tff(c_79,plain,(
    ! [A_51,B_52] :
      ( v1_relat_1(A_51)
      | ~ v1_relat_1(B_52)
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(resolution,[status(thm)],[c_8,c_68])).

tff(c_89,plain,(
    ! [A_1] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_79])).

tff(c_90,plain,(
    ! [A_1] : ~ v1_relat_1(A_1) ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_95,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_78])).

tff(c_96,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_1004,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_975,c_96])).

tff(c_1007,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_250,c_1004])).

tff(c_1009,plain,(
    v1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_233])).

tff(c_13104,plain,(
    ! [A_1867,A_1868] :
      ( A_1867 = '#skF_3'
      | ~ v1_funct_2(A_1867,A_1868,'#skF_3')
      | A_1868 = '#skF_3'
      | ~ r1_tarski(A_1867,k2_zfmisc_1(A_1868,'#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12848,c_12848,c_12848,c_12848,c_3824])).

tff(c_13127,plain,
    ( '#skF_5' = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_66,c_13104])).

tff(c_13136,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_13127])).

tff(c_13137,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_13136])).

tff(c_12849,plain,(
    k1_relat_1('#skF_5') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_12657])).

tff(c_13138,plain,(
    k1_relat_1('#skF_5') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13137,c_12849])).

tff(c_13148,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13137,c_52])).

tff(c_13144,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13137,c_117])).

tff(c_13146,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13137,c_66])).

tff(c_12532,plain,(
    ! [B_1791,C_1792] :
      ( k1_relset_1(k1_xboole_0,B_1791,C_1792) = k1_xboole_0
      | ~ v1_funct_2(C_1792,k1_xboole_0,B_1791)
      | ~ m1_subset_1(C_1792,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_1791))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_12554,plain,(
    ! [B_1791,A_6] :
      ( k1_relset_1(k1_xboole_0,B_1791,A_6) = k1_xboole_0
      | ~ v1_funct_2(A_6,k1_xboole_0,B_1791)
      | ~ r1_tarski(A_6,k2_zfmisc_1(k1_xboole_0,B_1791)) ) ),
    inference(resolution,[status(thm)],[c_8,c_12532])).

tff(c_13386,plain,(
    ! [B_1891,A_1892] :
      ( k1_relset_1('#skF_3',B_1891,A_1892) = '#skF_3'
      | ~ v1_funct_2(A_1892,'#skF_3',B_1891)
      | ~ r1_tarski(A_1892,k2_zfmisc_1('#skF_3',B_1891)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12848,c_12848,c_12848,c_12848,c_12554])).

tff(c_13393,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_13146,c_13386])).

tff(c_13417,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13148,c_13144,c_13393])).

tff(c_13419,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13138,c_13417])).

tff(c_13420,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_13136])).

tff(c_13436,plain,(
    v1_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13420,c_54])).

tff(c_149,plain,(
    ! [A_71,B_72,C_73] :
      ( r2_hidden('#skF_1'(A_71,B_72,C_73),B_72)
      | ~ r2_hidden(A_71,k9_relat_1(C_73,B_72))
      | ~ v1_relat_1(C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_156,plain,(
    ! [A_71,B_72,C_73,A_2] :
      ( r2_hidden('#skF_1'(A_71,B_72,C_73),A_2)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_2))
      | ~ r2_hidden(A_71,k9_relat_1(C_73,B_72))
      | ~ v1_relat_1(C_73) ) ),
    inference(resolution,[status(thm)],[c_149,c_4])).

tff(c_13952,plain,(
    ! [A_1977,B_1978,C_1979,A_1980] :
      ( r2_hidden('#skF_1'(A_1977,B_1978,C_1979),A_1980)
      | ~ m1_subset_1(B_1978,k1_zfmisc_1(A_1980))
      | ~ r2_hidden(A_1977,k9_relat_1(C_1979,B_1978))
      | ~ v1_relat_1(C_1979) ) ),
    inference(resolution,[status(thm)],[c_149,c_4])).

tff(c_13432,plain,(
    ! [F_40] :
      ( k1_funct_1('#skF_3',F_40) != '#skF_6'
      | ~ r2_hidden(F_40,'#skF_4')
      | ~ r2_hidden(F_40,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13420,c_46])).

tff(c_14014,plain,(
    ! [A_1986,B_1987,C_1988] :
      ( k1_funct_1('#skF_3','#skF_1'(A_1986,B_1987,C_1988)) != '#skF_6'
      | ~ r2_hidden('#skF_1'(A_1986,B_1987,C_1988),'#skF_4')
      | ~ m1_subset_1(B_1987,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_1986,k9_relat_1(C_1988,B_1987))
      | ~ v1_relat_1(C_1988) ) ),
    inference(resolution,[status(thm)],[c_13952,c_13432])).

tff(c_15866,plain,(
    ! [A_2237,B_2238,C_2239] :
      ( k1_funct_1('#skF_3','#skF_1'(A_2237,B_2238,C_2239)) != '#skF_6'
      | ~ m1_subset_1(B_2238,k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(B_2238,k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden(A_2237,k9_relat_1(C_2239,B_2238))
      | ~ v1_relat_1(C_2239) ) ),
    inference(resolution,[status(thm)],[c_156,c_14014])).

tff(c_15976,plain,(
    ! [B_2240,C_2241] :
      ( k1_funct_1('#skF_3','#skF_1'('#skF_6',B_2240,C_2241)) != '#skF_6'
      | ~ m1_subset_1(B_2240,k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(B_2240,k1_zfmisc_1('#skF_4'))
      | ~ v1_relat_1(C_2241) ) ),
    inference(resolution,[status(thm)],[c_7006,c_15866])).

tff(c_15979,plain,(
    ! [B_1803] :
      ( ~ m1_subset_1(B_1803,k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(B_1803,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12615,c_15976])).

tff(c_15983,plain,(
    ! [B_2242] :
      ( ~ m1_subset_1(B_2242,k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(B_2242,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1009,c_13436,c_15979])).

tff(c_15987,plain,(
    ! [D_2193,D_2195,D_2194,D_2196] : ~ m1_subset_1(k9_relat_1(k9_relat_1(k9_relat_1(k9_relat_1('#skF_3',D_2193),D_2195),D_2194),D_2196),k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_15614,c_15983])).

tff(c_16011,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15614,c_15987])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:18:31 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.67/3.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.78/3.65  
% 9.78/3.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.78/3.66  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 9.78/3.66  
% 9.78/3.66  %Foreground sorts:
% 9.78/3.66  
% 9.78/3.66  
% 9.78/3.66  %Background operators:
% 9.78/3.66  
% 9.78/3.66  
% 9.78/3.66  %Foreground operators:
% 9.78/3.66  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 9.78/3.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.78/3.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.78/3.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.78/3.66  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 9.78/3.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.78/3.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.78/3.66  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 9.78/3.66  tff('#skF_5', type, '#skF_5': $i).
% 9.78/3.66  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.78/3.66  tff('#skF_6', type, '#skF_6': $i).
% 9.78/3.66  tff('#skF_2', type, '#skF_2': $i).
% 9.78/3.66  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.78/3.66  tff('#skF_3', type, '#skF_3': $i).
% 9.78/3.66  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.78/3.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.78/3.66  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.78/3.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.78/3.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.78/3.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.78/3.66  tff('#skF_4', type, '#skF_4': $i).
% 9.78/3.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.78/3.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.78/3.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.78/3.66  
% 9.78/3.69  tff(f_47, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.78/3.69  tff(f_117, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_funct_2)).
% 9.78/3.69  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.78/3.69  tff(f_80, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 9.78/3.69  tff(f_58, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 9.78/3.69  tff(f_68, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 9.78/3.69  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.78/3.69  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 9.78/3.69  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.78/3.69  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.78/3.69  tff(f_72, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 9.78/3.69  tff(f_34, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 9.78/3.69  tff(c_12, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.78/3.69  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.78/3.69  tff(c_68, plain, (![B_49, A_50]: (v1_relat_1(B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.78/3.69  tff(c_74, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_50, c_68])).
% 9.78/3.69  tff(c_78, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_74])).
% 9.78/3.69  tff(c_54, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.78/3.69  tff(c_159, plain, (![A_77, B_78, C_79, D_80]: (k7_relset_1(A_77, B_78, C_79, D_80)=k9_relat_1(C_79, D_80) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.78/3.69  tff(c_166, plain, (![D_80]: (k7_relset_1('#skF_2', '#skF_3', '#skF_5', D_80)=k9_relat_1('#skF_5', D_80))), inference(resolution, [status(thm)], [c_50, c_159])).
% 9.78/3.69  tff(c_48, plain, (r2_hidden('#skF_6', k7_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.78/3.69  tff(c_169, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_166, c_48])).
% 9.78/3.69  tff(c_16, plain, (![A_13, B_14, C_15]: (r2_hidden('#skF_1'(A_13, B_14, C_15), B_14) | ~r2_hidden(A_13, k9_relat_1(C_15, B_14)) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.78/3.69  tff(c_4108, plain, (![A_683, B_684, C_685]: (r2_hidden(k4_tarski('#skF_1'(A_683, B_684, C_685), A_683), C_685) | ~r2_hidden(A_683, k9_relat_1(C_685, B_684)) | ~v1_relat_1(C_685))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.78/3.69  tff(c_24, plain, (![C_21, A_19, B_20]: (k1_funct_1(C_21, A_19)=B_20 | ~r2_hidden(k4_tarski(A_19, B_20), C_21) | ~v1_funct_1(C_21) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.78/3.69  tff(c_4439, plain, (![C_743, A_744, B_745]: (k1_funct_1(C_743, '#skF_1'(A_744, B_745, C_743))=A_744 | ~v1_funct_1(C_743) | ~r2_hidden(A_744, k9_relat_1(C_743, B_745)) | ~v1_relat_1(C_743))), inference(resolution, [status(thm)], [c_4108, c_24])).
% 9.78/3.69  tff(c_4456, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_169, c_4439])).
% 9.78/3.69  tff(c_4467, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_54, c_4456])).
% 9.78/3.69  tff(c_52, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.78/3.69  tff(c_108, plain, (![A_58, B_59, C_60]: (k1_relset_1(A_58, B_59, C_60)=k1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.78/3.69  tff(c_117, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_108])).
% 9.78/3.69  tff(c_4491, plain, (![B_746, A_747, C_748]: (k1_xboole_0=B_746 | k1_relset_1(A_747, B_746, C_748)=A_747 | ~v1_funct_2(C_748, A_747, B_746) | ~m1_subset_1(C_748, k1_zfmisc_1(k2_zfmisc_1(A_747, B_746))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.78/3.69  tff(c_4510, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_4491])).
% 9.78/3.69  tff(c_4519, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_117, c_4510])).
% 9.78/3.69  tff(c_4520, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(splitLeft, [status(thm)], [c_4519])).
% 9.78/3.69  tff(c_20, plain, (![A_13, B_14, C_15]: (r2_hidden('#skF_1'(A_13, B_14, C_15), k1_relat_1(C_15)) | ~r2_hidden(A_13, k9_relat_1(C_15, B_14)) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.78/3.69  tff(c_22, plain, (![A_19, C_21]: (r2_hidden(k4_tarski(A_19, k1_funct_1(C_21, A_19)), C_21) | ~r2_hidden(A_19, k1_relat_1(C_21)) | ~v1_funct_1(C_21) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.78/3.69  tff(c_4472, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_6'), '#skF_5') | ~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4467, c_22])).
% 9.78/3.69  tff(c_4476, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_6'), '#skF_5') | ~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_54, c_4472])).
% 9.78/3.69  tff(c_4478, plain, (~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_4476])).
% 9.78/3.69  tff(c_4481, plain, (~r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_20, c_4478])).
% 9.78/3.69  tff(c_4485, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_169, c_4481])).
% 9.78/3.69  tff(c_4487, plain, (r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_4476])).
% 9.78/3.69  tff(c_4521, plain, (r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4520, c_4487])).
% 9.78/3.69  tff(c_46, plain, (![F_40]: (k1_funct_1('#skF_5', F_40)!='#skF_6' | ~r2_hidden(F_40, '#skF_4') | ~r2_hidden(F_40, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.78/3.69  tff(c_4541, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6' | ~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_4521, c_46])).
% 9.78/3.69  tff(c_4545, plain, (~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4467, c_4541])).
% 9.78/3.69  tff(c_4548, plain, (~r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_16, c_4545])).
% 9.78/3.69  tff(c_4552, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_169, c_4548])).
% 9.78/3.69  tff(c_4553, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_4519])).
% 9.78/3.69  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.78/3.69  tff(c_4590, plain, (![A_1]: (r1_tarski('#skF_3', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_4553, c_2])).
% 9.78/3.69  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.78/3.69  tff(c_189, plain, (![A_84, B_85, A_86, D_87]: (k7_relset_1(A_84, B_85, A_86, D_87)=k9_relat_1(A_86, D_87) | ~r1_tarski(A_86, k2_zfmisc_1(A_84, B_85)))), inference(resolution, [status(thm)], [c_8, c_159])).
% 9.78/3.69  tff(c_2791, plain, (![A_476, B_477, D_478]: (k7_relset_1(A_476, B_477, k1_xboole_0, D_478)=k9_relat_1(k1_xboole_0, D_478))), inference(resolution, [status(thm)], [c_2, c_189])).
% 9.78/3.69  tff(c_28, plain, (![A_22, B_23, C_24, D_25]: (m1_subset_1(k7_relset_1(A_22, B_23, C_24, D_25), k1_zfmisc_1(B_23)) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.78/3.69  tff(c_3869, plain, (![D_638, B_639, A_640]: (m1_subset_1(k9_relat_1(k1_xboole_0, D_638), k1_zfmisc_1(B_639)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_640, B_639))))), inference(superposition, [status(thm), theory('equality')], [c_2791, c_28])).
% 9.78/3.69  tff(c_3872, plain, (![D_638, B_639, A_640]: (m1_subset_1(k9_relat_1(k1_xboole_0, D_638), k1_zfmisc_1(B_639)) | ~r1_tarski(k1_xboole_0, k2_zfmisc_1(A_640, B_639)))), inference(resolution, [status(thm)], [c_8, c_3869])).
% 9.78/3.69  tff(c_3877, plain, (![D_641, B_642]: (m1_subset_1(k9_relat_1(k1_xboole_0, D_641), k1_zfmisc_1(B_642)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_3872])).
% 9.78/3.69  tff(c_198, plain, (![A_88, B_89, C_90, D_91]: (m1_subset_1(k7_relset_1(A_88, B_89, C_90, D_91), k1_zfmisc_1(B_89)) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.78/3.69  tff(c_214, plain, (![D_80]: (m1_subset_1(k9_relat_1('#skF_5', D_80), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_166, c_198])).
% 9.78/3.69  tff(c_221, plain, (![D_92]: (m1_subset_1(k9_relat_1('#skF_5', D_92), k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_214])).
% 9.78/3.69  tff(c_97, plain, (![C_53, A_54, B_55]: (r2_hidden(C_53, A_54) | ~r2_hidden(C_53, B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.78/3.69  tff(c_100, plain, (![A_54]: (r2_hidden('#skF_6', A_54) | ~m1_subset_1(k7_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1(A_54)))), inference(resolution, [status(thm)], [c_48, c_97])).
% 9.78/3.69  tff(c_168, plain, (![A_54]: (r2_hidden('#skF_6', A_54) | ~m1_subset_1(k9_relat_1('#skF_5', '#skF_4'), k1_zfmisc_1(A_54)))), inference(demodulation, [status(thm), theory('equality')], [c_166, c_100])).
% 9.78/3.69  tff(c_232, plain, (r2_hidden('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_221, c_168])).
% 9.78/3.69  tff(c_4, plain, (![C_5, A_2, B_3]: (r2_hidden(C_5, A_2) | ~r2_hidden(C_5, B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.78/3.69  tff(c_1017, plain, (![A_219]: (r2_hidden('#skF_6', A_219) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_219)))), inference(resolution, [status(thm)], [c_232, c_4])).
% 9.78/3.69  tff(c_1023, plain, (![B_220]: (r2_hidden('#skF_6', B_220) | ~r1_tarski('#skF_3', B_220))), inference(resolution, [status(thm)], [c_8, c_1017])).
% 9.78/3.69  tff(c_1030, plain, (![A_2, B_220]: (r2_hidden('#skF_6', A_2) | ~m1_subset_1(B_220, k1_zfmisc_1(A_2)) | ~r1_tarski('#skF_3', B_220))), inference(resolution, [status(thm)], [c_1023, c_4])).
% 9.78/3.69  tff(c_3907, plain, (![B_642, D_641]: (r2_hidden('#skF_6', B_642) | ~r1_tarski('#skF_3', k9_relat_1(k1_xboole_0, D_641)))), inference(resolution, [status(thm)], [c_3877, c_1030])).
% 9.78/3.69  tff(c_3957, plain, (![D_641]: (~r1_tarski('#skF_3', k9_relat_1(k1_xboole_0, D_641)))), inference(splitLeft, [status(thm)], [c_3907])).
% 9.78/3.69  tff(c_4580, plain, (![D_641]: (~r1_tarski('#skF_3', k9_relat_1('#skF_3', D_641)))), inference(demodulation, [status(thm), theory('equality')], [c_4553, c_3957])).
% 9.78/3.69  tff(c_4737, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4590, c_4580])).
% 9.78/3.69  tff(c_4738, plain, (![B_642]: (r2_hidden('#skF_6', B_642))), inference(splitRight, [status(thm)], [c_3907])).
% 9.78/3.69  tff(c_5833, plain, (![A_926, B_927, C_928]: (r2_hidden(k4_tarski('#skF_1'(A_926, B_927, C_928), A_926), C_928) | ~r2_hidden(A_926, k9_relat_1(C_928, B_927)) | ~v1_relat_1(C_928))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.78/3.69  tff(c_6018, plain, (![C_957, A_958, B_959]: (k1_funct_1(C_957, '#skF_1'(A_958, B_959, C_957))=A_958 | ~v1_funct_1(C_957) | ~r2_hidden(A_958, k9_relat_1(C_957, B_959)) | ~v1_relat_1(C_957))), inference(resolution, [status(thm)], [c_5833, c_24])).
% 9.78/3.69  tff(c_6033, plain, (![C_957, B_959]: (k1_funct_1(C_957, '#skF_1'('#skF_6', B_959, C_957))='#skF_6' | ~v1_funct_1(C_957) | ~v1_relat_1(C_957))), inference(resolution, [status(thm)], [c_4738, c_6018])).
% 9.78/3.69  tff(c_6347, plain, (![B_1006, A_1007, C_1008]: (k1_xboole_0=B_1006 | k1_relset_1(A_1007, B_1006, C_1008)=A_1007 | ~v1_funct_2(C_1008, A_1007, B_1006) | ~m1_subset_1(C_1008, k1_zfmisc_1(k2_zfmisc_1(A_1007, B_1006))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.78/3.69  tff(c_6370, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_6347])).
% 9.78/3.69  tff(c_6380, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_117, c_6370])).
% 9.78/3.69  tff(c_6381, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(splitLeft, [status(thm)], [c_6380])).
% 9.78/3.69  tff(c_6386, plain, (![A_13, B_14]: (r2_hidden('#skF_1'(A_13, B_14, '#skF_5'), '#skF_2') | ~r2_hidden(A_13, k9_relat_1('#skF_5', B_14)) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_6381, c_20])).
% 9.78/3.69  tff(c_6396, plain, (![A_1009, B_1010]: (r2_hidden('#skF_1'(A_1009, B_1010, '#skF_5'), '#skF_2') | ~r2_hidden(A_1009, k9_relat_1('#skF_5', B_1010)))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_6386])).
% 9.78/3.69  tff(c_6522, plain, (![A_1029, B_1030]: (k1_funct_1('#skF_5', '#skF_1'(A_1029, B_1030, '#skF_5'))!='#skF_6' | ~r2_hidden('#skF_1'(A_1029, B_1030, '#skF_5'), '#skF_4') | ~r2_hidden(A_1029, k9_relat_1('#skF_5', B_1030)))), inference(resolution, [status(thm)], [c_6396, c_46])).
% 9.78/3.69  tff(c_6530, plain, (![A_13]: (k1_funct_1('#skF_5', '#skF_1'(A_13, '#skF_4', '#skF_5'))!='#skF_6' | ~r2_hidden(A_13, k9_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_16, c_6522])).
% 9.78/3.69  tff(c_6545, plain, (![A_1033]: (k1_funct_1('#skF_5', '#skF_1'(A_1033, '#skF_4', '#skF_5'))!='#skF_6' | ~r2_hidden(A_1033, k9_relat_1('#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_6530])).
% 9.78/3.69  tff(c_6587, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6'), inference(resolution, [status(thm)], [c_4738, c_6545])).
% 9.78/3.69  tff(c_6591, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6033, c_6587])).
% 9.78/3.69  tff(c_6595, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_54, c_6591])).
% 9.78/3.69  tff(c_6596, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_6380])).
% 9.78/3.69  tff(c_6635, plain, (![A_1]: (r1_tarski('#skF_3', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_6596, c_2])).
% 9.78/3.69  tff(c_58, plain, (![A_46, B_47]: (r1_tarski(A_46, B_47) | ~m1_subset_1(A_46, k1_zfmisc_1(B_47)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.78/3.69  tff(c_66, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_50, c_58])).
% 9.78/3.69  tff(c_3814, plain, (![C_627, A_628]: (k1_xboole_0=C_627 | ~v1_funct_2(C_627, A_628, k1_xboole_0) | k1_xboole_0=A_628 | ~m1_subset_1(C_627, k1_zfmisc_1(k2_zfmisc_1(A_628, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.78/3.69  tff(c_3824, plain, (![A_6, A_628]: (k1_xboole_0=A_6 | ~v1_funct_2(A_6, A_628, k1_xboole_0) | k1_xboole_0=A_628 | ~r1_tarski(A_6, k2_zfmisc_1(A_628, k1_xboole_0)))), inference(resolution, [status(thm)], [c_8, c_3814])).
% 9.78/3.69  tff(c_6720, plain, (![A_1047, A_1048]: (A_1047='#skF_3' | ~v1_funct_2(A_1047, A_1048, '#skF_3') | A_1048='#skF_3' | ~r1_tarski(A_1047, k2_zfmisc_1(A_1048, '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_6596, c_6596, c_6596, c_6596, c_3824])).
% 9.78/3.69  tff(c_6735, plain, ('#skF_5'='#skF_3' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_66, c_6720])).
% 9.78/3.69  tff(c_6742, plain, ('#skF_5'='#skF_3' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_6735])).
% 9.78/3.69  tff(c_6743, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_6742])).
% 9.78/3.69  tff(c_6597, plain, (k1_relat_1('#skF_5')!='#skF_2'), inference(splitRight, [status(thm)], [c_6380])).
% 9.78/3.69  tff(c_6744, plain, (k1_relat_1('#skF_5')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6743, c_6597])).
% 9.78/3.69  tff(c_6754, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6743, c_52])).
% 9.78/3.69  tff(c_6750, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6743, c_117])).
% 9.78/3.69  tff(c_6752, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6743, c_66])).
% 9.78/3.69  tff(c_4769, plain, (![B_764, C_765]: (k1_relset_1(k1_xboole_0, B_764, C_765)=k1_xboole_0 | ~v1_funct_2(C_765, k1_xboole_0, B_764) | ~m1_subset_1(C_765, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_764))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.78/3.69  tff(c_4784, plain, (![B_764, A_6]: (k1_relset_1(k1_xboole_0, B_764, A_6)=k1_xboole_0 | ~v1_funct_2(A_6, k1_xboole_0, B_764) | ~r1_tarski(A_6, k2_zfmisc_1(k1_xboole_0, B_764)))), inference(resolution, [status(thm)], [c_8, c_4769])).
% 9.78/3.69  tff(c_6959, plain, (![B_1064, A_1065]: (k1_relset_1('#skF_3', B_1064, A_1065)='#skF_3' | ~v1_funct_2(A_1065, '#skF_3', B_1064) | ~r1_tarski(A_1065, k2_zfmisc_1('#skF_3', B_1064)))), inference(demodulation, [status(thm), theory('equality')], [c_6596, c_6596, c_6596, c_6596, c_4784])).
% 9.78/3.69  tff(c_6966, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_6752, c_6959])).
% 9.78/3.69  tff(c_6982, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6754, c_6750, c_6966])).
% 9.78/3.69  tff(c_6984, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6744, c_6982])).
% 9.78/3.69  tff(c_6985, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_6742])).
% 9.78/3.69  tff(c_3408, plain, (![B_583, A_584, C_585]: (k1_xboole_0=B_583 | k1_relset_1(A_584, B_583, C_585)=A_584 | ~v1_funct_2(C_585, A_584, B_583) | ~m1_subset_1(C_585, k1_zfmisc_1(k2_zfmisc_1(A_584, B_583))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.78/3.69  tff(c_3427, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_3408])).
% 9.78/3.69  tff(c_3435, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_117, c_3427])).
% 9.78/3.69  tff(c_3436, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(splitLeft, [status(thm)], [c_3435])).
% 9.78/3.69  tff(c_3441, plain, (![A_13, B_14]: (r2_hidden('#skF_1'(A_13, B_14, '#skF_5'), '#skF_2') | ~r2_hidden(A_13, k9_relat_1('#skF_5', B_14)) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3436, c_20])).
% 9.78/3.69  tff(c_3451, plain, (![A_586, B_587]: (r2_hidden('#skF_1'(A_586, B_587, '#skF_5'), '#skF_2') | ~r2_hidden(A_586, k9_relat_1('#skF_5', B_587)))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_3441])).
% 9.78/3.69  tff(c_3612, plain, (![A_612, B_613]: (k1_funct_1('#skF_5', '#skF_1'(A_612, B_613, '#skF_5'))!='#skF_6' | ~r2_hidden('#skF_1'(A_612, B_613, '#skF_5'), '#skF_4') | ~r2_hidden(A_612, k9_relat_1('#skF_5', B_613)))), inference(resolution, [status(thm)], [c_3451, c_46])).
% 9.78/3.69  tff(c_3620, plain, (![A_13]: (k1_funct_1('#skF_5', '#skF_1'(A_13, '#skF_4', '#skF_5'))!='#skF_6' | ~r2_hidden(A_13, k9_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_16, c_3612])).
% 9.78/3.69  tff(c_3625, plain, (![A_614]: (k1_funct_1('#skF_5', '#skF_1'(A_614, '#skF_4', '#skF_5'))!='#skF_6' | ~r2_hidden(A_614, k9_relat_1('#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_3620])).
% 9.78/3.69  tff(c_3662, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6'), inference(resolution, [status(thm)], [c_169, c_3625])).
% 9.78/3.69  tff(c_2905, plain, (![A_495, B_496, C_497]: (r2_hidden(k4_tarski('#skF_1'(A_495, B_496, C_497), A_495), C_497) | ~r2_hidden(A_495, k9_relat_1(C_497, B_496)) | ~v1_relat_1(C_497))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.78/3.69  tff(c_3664, plain, (![C_615, A_616, B_617]: (k1_funct_1(C_615, '#skF_1'(A_616, B_617, C_615))=A_616 | ~v1_funct_1(C_615) | ~r2_hidden(A_616, k9_relat_1(C_615, B_617)) | ~v1_relat_1(C_615))), inference(resolution, [status(thm)], [c_2905, c_24])).
% 9.78/3.69  tff(c_3681, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_169, c_3664])).
% 9.78/3.69  tff(c_3692, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_54, c_3681])).
% 9.78/3.69  tff(c_3694, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3662, c_3692])).
% 9.78/3.69  tff(c_3695, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_3435])).
% 9.78/3.69  tff(c_3754, plain, (![A_1]: (r1_tarski('#skF_3', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_3695, c_2])).
% 9.78/3.69  tff(c_2803, plain, (![A_479, B_480]: (r2_hidden('#skF_6', A_479) | ~m1_subset_1(B_480, k1_zfmisc_1(A_479)) | ~r1_tarski('#skF_3', B_480))), inference(resolution, [status(thm)], [c_1023, c_4])).
% 9.78/3.69  tff(c_2820, plain, (r2_hidden('#skF_6', k2_zfmisc_1('#skF_2', '#skF_3')) | ~r1_tarski('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_2803])).
% 9.78/3.69  tff(c_2821, plain, (~r1_tarski('#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_2820])).
% 9.78/3.69  tff(c_3771, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3754, c_2821])).
% 9.78/3.69  tff(c_3773, plain, (r1_tarski('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_2820])).
% 9.78/3.69  tff(c_3783, plain, (![B_622, A_623]: (r2_hidden('#skF_6', B_622) | ~r1_tarski('#skF_3', A_623) | ~r1_tarski(A_623, B_622))), inference(resolution, [status(thm)], [c_8, c_2803])).
% 9.78/3.69  tff(c_3790, plain, (![B_624]: (r2_hidden('#skF_6', B_624) | ~r1_tarski('#skF_5', B_624))), inference(resolution, [status(thm)], [c_3773, c_3783])).
% 9.78/3.69  tff(c_3797, plain, (![A_2, B_624]: (r2_hidden('#skF_6', A_2) | ~m1_subset_1(B_624, k1_zfmisc_1(A_2)) | ~r1_tarski('#skF_5', B_624))), inference(resolution, [status(thm)], [c_3790, c_4])).
% 9.78/3.69  tff(c_3904, plain, (![B_642, D_641]: (r2_hidden('#skF_6', B_642) | ~r1_tarski('#skF_5', k9_relat_1(k1_xboole_0, D_641)))), inference(resolution, [status(thm)], [c_3877, c_3797])).
% 9.78/3.69  tff(c_3955, plain, (![D_641]: (~r1_tarski('#skF_5', k9_relat_1(k1_xboole_0, D_641)))), inference(splitLeft, [status(thm)], [c_3904])).
% 9.78/3.69  tff(c_6626, plain, (![D_641]: (~r1_tarski('#skF_5', k9_relat_1('#skF_3', D_641)))), inference(demodulation, [status(thm), theory('equality')], [c_6596, c_3955])).
% 9.78/3.69  tff(c_6987, plain, (![D_641]: (~r1_tarski('#skF_3', k9_relat_1('#skF_3', D_641)))), inference(demodulation, [status(thm), theory('equality')], [c_6985, c_6626])).
% 9.78/3.69  tff(c_7005, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6635, c_6987])).
% 9.78/3.69  tff(c_7006, plain, (![B_642]: (r2_hidden('#skF_6', B_642))), inference(splitRight, [status(thm)], [c_3904])).
% 9.78/3.69  tff(c_12297, plain, (![A_1746, B_1747, C_1748]: (r2_hidden(k4_tarski('#skF_1'(A_1746, B_1747, C_1748), A_1746), C_1748) | ~r2_hidden(A_1746, k9_relat_1(C_1748, B_1747)) | ~v1_relat_1(C_1748))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.78/3.69  tff(c_12600, plain, (![C_1801, A_1802, B_1803]: (k1_funct_1(C_1801, '#skF_1'(A_1802, B_1803, C_1801))=A_1802 | ~v1_funct_1(C_1801) | ~r2_hidden(A_1802, k9_relat_1(C_1801, B_1803)) | ~v1_relat_1(C_1801))), inference(resolution, [status(thm)], [c_12297, c_24])).
% 9.78/3.69  tff(c_12615, plain, (![C_1801, B_1803]: (k1_funct_1(C_1801, '#skF_1'('#skF_6', B_1803, C_1801))='#skF_6' | ~v1_funct_1(C_1801) | ~v1_relat_1(C_1801))), inference(resolution, [status(thm)], [c_7006, c_12600])).
% 9.78/3.69  tff(c_12629, plain, (![B_1806, A_1807, C_1808]: (k1_xboole_0=B_1806 | k1_relset_1(A_1807, B_1806, C_1808)=A_1807 | ~v1_funct_2(C_1808, A_1807, B_1806) | ~m1_subset_1(C_1808, k1_zfmisc_1(k2_zfmisc_1(A_1807, B_1806))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.78/3.69  tff(c_12648, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_12629])).
% 9.78/3.69  tff(c_12657, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_117, c_12648])).
% 9.78/3.69  tff(c_12658, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(splitLeft, [status(thm)], [c_12657])).
% 9.78/3.69  tff(c_12663, plain, (![A_13, B_14]: (r2_hidden('#skF_1'(A_13, B_14, '#skF_5'), '#skF_2') | ~r2_hidden(A_13, k9_relat_1('#skF_5', B_14)) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_12658, c_20])).
% 9.78/3.69  tff(c_12673, plain, (![A_1809, B_1810]: (r2_hidden('#skF_1'(A_1809, B_1810, '#skF_5'), '#skF_2') | ~r2_hidden(A_1809, k9_relat_1('#skF_5', B_1810)))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_12663])).
% 9.78/3.69  tff(c_12798, plain, (![A_1828, B_1829]: (k1_funct_1('#skF_5', '#skF_1'(A_1828, B_1829, '#skF_5'))!='#skF_6' | ~r2_hidden('#skF_1'(A_1828, B_1829, '#skF_5'), '#skF_4') | ~r2_hidden(A_1828, k9_relat_1('#skF_5', B_1829)))), inference(resolution, [status(thm)], [c_12673, c_46])).
% 9.78/3.69  tff(c_12806, plain, (![A_13]: (k1_funct_1('#skF_5', '#skF_1'(A_13, '#skF_4', '#skF_5'))!='#skF_6' | ~r2_hidden(A_13, k9_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_16, c_12798])).
% 9.78/3.69  tff(c_12811, plain, (![A_1830]: (k1_funct_1('#skF_5', '#skF_1'(A_1830, '#skF_4', '#skF_5'))!='#skF_6' | ~r2_hidden(A_1830, k9_relat_1('#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_12806])).
% 9.78/3.69  tff(c_12839, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6'), inference(resolution, [status(thm)], [c_7006, c_12811])).
% 9.78/3.69  tff(c_12843, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_12615, c_12839])).
% 9.78/3.69  tff(c_12847, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_54, c_12843])).
% 9.78/3.69  tff(c_12848, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_12657])).
% 9.78/3.69  tff(c_3875, plain, (![D_638, B_639]: (m1_subset_1(k9_relat_1(k1_xboole_0, D_638), k1_zfmisc_1(B_639)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_3872])).
% 9.78/3.69  tff(c_32, plain, (![A_29, B_30, C_31, D_32]: (k7_relset_1(A_29, B_30, C_31, D_32)=k9_relat_1(C_31, D_32) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.78/3.69  tff(c_7049, plain, (![A_1072, B_1073, D_1074, D_1075]: (k7_relset_1(A_1072, B_1073, k9_relat_1(k1_xboole_0, D_1074), D_1075)=k9_relat_1(k9_relat_1(k1_xboole_0, D_1074), D_1075))), inference(resolution, [status(thm)], [c_3877, c_32])).
% 9.78/3.69  tff(c_7055, plain, (![D_1074, D_1075, B_1073, A_1072]: (m1_subset_1(k9_relat_1(k9_relat_1(k1_xboole_0, D_1074), D_1075), k1_zfmisc_1(B_1073)) | ~m1_subset_1(k9_relat_1(k1_xboole_0, D_1074), k1_zfmisc_1(k2_zfmisc_1(A_1072, B_1073))))), inference(superposition, [status(thm), theory('equality')], [c_7049, c_28])).
% 9.78/3.69  tff(c_7061, plain, (![D_1074, D_1075, B_1073]: (m1_subset_1(k9_relat_1(k9_relat_1(k1_xboole_0, D_1074), D_1075), k1_zfmisc_1(B_1073)))), inference(demodulation, [status(thm), theory('equality')], [c_3875, c_7055])).
% 9.78/3.69  tff(c_12866, plain, (![D_1074, D_1075, B_1073]: (m1_subset_1(k9_relat_1(k9_relat_1('#skF_3', D_1074), D_1075), k1_zfmisc_1(B_1073)))), inference(demodulation, [status(thm), theory('equality')], [c_12848, c_7061])).
% 9.78/3.69  tff(c_7063, plain, (![D_1076, D_1077, B_1078]: (m1_subset_1(k9_relat_1(k9_relat_1(k1_xboole_0, D_1076), D_1077), k1_zfmisc_1(B_1078)))), inference(demodulation, [status(thm), theory('equality')], [c_3875, c_7055])).
% 9.78/3.69  tff(c_7082, plain, (![A_29, D_1077, D_1076, D_32, B_30]: (k7_relset_1(A_29, B_30, k9_relat_1(k9_relat_1(k1_xboole_0, D_1076), D_1077), D_32)=k9_relat_1(k9_relat_1(k9_relat_1(k1_xboole_0, D_1076), D_1077), D_32))), inference(resolution, [status(thm)], [c_7063, c_32])).
% 9.78/3.69  tff(c_14028, plain, (![B_1991, D_1993, D_1990, D_1989, A_1992]: (k7_relset_1(A_1992, B_1991, k9_relat_1(k9_relat_1('#skF_3', D_1990), D_1993), D_1989)=k9_relat_1(k9_relat_1(k9_relat_1('#skF_3', D_1990), D_1993), D_1989))), inference(demodulation, [status(thm), theory('equality')], [c_12848, c_12848, c_7082])).
% 9.78/3.69  tff(c_14037, plain, (![B_1991, D_1993, D_1990, D_1989, A_1992]: (m1_subset_1(k9_relat_1(k9_relat_1(k9_relat_1('#skF_3', D_1990), D_1993), D_1989), k1_zfmisc_1(B_1991)) | ~m1_subset_1(k9_relat_1(k9_relat_1('#skF_3', D_1990), D_1993), k1_zfmisc_1(k2_zfmisc_1(A_1992, B_1991))))), inference(superposition, [status(thm), theory('equality')], [c_14028, c_28])).
% 9.78/3.69  tff(c_14045, plain, (![D_1990, D_1993, D_1989, B_1991]: (m1_subset_1(k9_relat_1(k9_relat_1(k9_relat_1('#skF_3', D_1990), D_1993), D_1989), k1_zfmisc_1(B_1991)))), inference(demodulation, [status(thm), theory('equality')], [c_12866, c_14037])).
% 9.78/3.69  tff(c_14025, plain, (![A_29, D_1077, D_1076, D_32, B_30]: (k7_relset_1(A_29, B_30, k9_relat_1(k9_relat_1('#skF_3', D_1076), D_1077), D_32)=k9_relat_1(k9_relat_1(k9_relat_1('#skF_3', D_1076), D_1077), D_32))), inference(demodulation, [status(thm), theory('equality')], [c_12848, c_12848, c_7082])).
% 9.78/3.69  tff(c_14848, plain, (![D_2101, B_2102, A_2104, A_2103, C_2105, D_2100]: (k7_relset_1(A_2103, B_2102, k7_relset_1(A_2104, k2_zfmisc_1(A_2103, B_2102), C_2105, D_2101), D_2100)=k9_relat_1(k7_relset_1(A_2104, k2_zfmisc_1(A_2103, B_2102), C_2105, D_2101), D_2100) | ~m1_subset_1(C_2105, k1_zfmisc_1(k2_zfmisc_1(A_2104, k2_zfmisc_1(A_2103, B_2102)))))), inference(resolution, [status(thm)], [c_198, c_32])).
% 9.78/3.69  tff(c_14854, plain, (![D_2101, D_1074, D_1075, B_2102, A_2104, A_2103, D_2100]: (k7_relset_1(A_2103, B_2102, k7_relset_1(A_2104, k2_zfmisc_1(A_2103, B_2102), k9_relat_1(k9_relat_1('#skF_3', D_1074), D_1075), D_2101), D_2100)=k9_relat_1(k7_relset_1(A_2104, k2_zfmisc_1(A_2103, B_2102), k9_relat_1(k9_relat_1('#skF_3', D_1074), D_1075), D_2101), D_2100))), inference(resolution, [status(thm)], [c_12866, c_14848])).
% 9.78/3.69  tff(c_15587, plain, (![A_2197, D_2194, B_2192, D_2195, D_2196, D_2193]: (k7_relset_1(A_2197, B_2192, k9_relat_1(k9_relat_1(k9_relat_1('#skF_3', D_2193), D_2195), D_2194), D_2196)=k9_relat_1(k9_relat_1(k9_relat_1(k9_relat_1('#skF_3', D_2193), D_2195), D_2194), D_2196))), inference(demodulation, [status(thm), theory('equality')], [c_14025, c_14025, c_14854])).
% 9.78/3.69  tff(c_15602, plain, (![A_2197, D_2194, B_2192, D_2195, D_2196, D_2193]: (m1_subset_1(k9_relat_1(k9_relat_1(k9_relat_1(k9_relat_1('#skF_3', D_2193), D_2195), D_2194), D_2196), k1_zfmisc_1(B_2192)) | ~m1_subset_1(k9_relat_1(k9_relat_1(k9_relat_1('#skF_3', D_2193), D_2195), D_2194), k1_zfmisc_1(k2_zfmisc_1(A_2197, B_2192))))), inference(superposition, [status(thm), theory('equality')], [c_15587, c_28])).
% 9.78/3.69  tff(c_15614, plain, (![D_2194, B_2192, D_2195, D_2196, D_2193]: (m1_subset_1(k9_relat_1(k9_relat_1(k9_relat_1(k9_relat_1('#skF_3', D_2193), D_2195), D_2194), D_2196), k1_zfmisc_1(B_2192)))), inference(demodulation, [status(thm), theory('equality')], [c_14045, c_15602])).
% 9.78/3.69  tff(c_10, plain, (![B_10, A_8]: (v1_relat_1(B_10) | ~m1_subset_1(B_10, k1_zfmisc_1(A_8)) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.78/3.69  tff(c_233, plain, (![D_92]: (v1_relat_1(k9_relat_1('#skF_5', D_92)) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_221, c_10])).
% 9.78/3.69  tff(c_250, plain, (~v1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_233])).
% 9.78/3.69  tff(c_572, plain, (![A_159, B_160, C_161]: (r2_hidden(k4_tarski('#skF_1'(A_159, B_160, C_161), A_159), C_161) | ~r2_hidden(A_159, k9_relat_1(C_161, B_160)) | ~v1_relat_1(C_161))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.78/3.69  tff(c_893, plain, (![C_209, A_210, B_211]: (k1_funct_1(C_209, '#skF_1'(A_210, B_211, C_209))=A_210 | ~v1_funct_1(C_209) | ~r2_hidden(A_210, k9_relat_1(C_209, B_211)) | ~v1_relat_1(C_209))), inference(resolution, [status(thm)], [c_572, c_24])).
% 9.78/3.69  tff(c_907, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_169, c_893])).
% 9.78/3.69  tff(c_917, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_54, c_907])).
% 9.78/3.69  tff(c_736, plain, (![B_183, A_184, C_185]: (k1_xboole_0=B_183 | k1_relset_1(A_184, B_183, C_185)=A_184 | ~v1_funct_2(C_185, A_184, B_183) | ~m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1(A_184, B_183))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.78/3.69  tff(c_755, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_736])).
% 9.78/3.69  tff(c_763, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_117, c_755])).
% 9.78/3.69  tff(c_771, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(splitLeft, [status(thm)], [c_763])).
% 9.78/3.69  tff(c_776, plain, (![A_13, B_14]: (r2_hidden('#skF_1'(A_13, B_14, '#skF_5'), '#skF_2') | ~r2_hidden(A_13, k9_relat_1('#skF_5', B_14)) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_771, c_20])).
% 9.78/3.69  tff(c_786, plain, (![A_187, B_188]: (r2_hidden('#skF_1'(A_187, B_188, '#skF_5'), '#skF_2') | ~r2_hidden(A_187, k9_relat_1('#skF_5', B_188)))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_776])).
% 9.78/3.69  tff(c_919, plain, (![A_212, B_213]: (k1_funct_1('#skF_5', '#skF_1'(A_212, B_213, '#skF_5'))!='#skF_6' | ~r2_hidden('#skF_1'(A_212, B_213, '#skF_5'), '#skF_4') | ~r2_hidden(A_212, k9_relat_1('#skF_5', B_213)))), inference(resolution, [status(thm)], [c_786, c_46])).
% 9.78/3.69  tff(c_927, plain, (![A_13]: (k1_funct_1('#skF_5', '#skF_1'(A_13, '#skF_4', '#skF_5'))!='#skF_6' | ~r2_hidden(A_13, k9_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_16, c_919])).
% 9.78/3.69  tff(c_941, plain, (![A_214]: (k1_funct_1('#skF_5', '#skF_1'(A_214, '#skF_4', '#skF_5'))!='#skF_6' | ~r2_hidden(A_214, k9_relat_1('#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_927])).
% 9.78/3.69  tff(c_960, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6'), inference(resolution, [status(thm)], [c_169, c_941])).
% 9.78/3.69  tff(c_974, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_917, c_960])).
% 9.78/3.69  tff(c_975, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_763])).
% 9.78/3.69  tff(c_79, plain, (![A_51, B_52]: (v1_relat_1(A_51) | ~v1_relat_1(B_52) | ~r1_tarski(A_51, B_52))), inference(resolution, [status(thm)], [c_8, c_68])).
% 9.78/3.69  tff(c_89, plain, (![A_1]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_1))), inference(resolution, [status(thm)], [c_2, c_79])).
% 9.78/3.69  tff(c_90, plain, (![A_1]: (~v1_relat_1(A_1))), inference(splitLeft, [status(thm)], [c_89])).
% 9.78/3.69  tff(c_95, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_78])).
% 9.78/3.69  tff(c_96, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_89])).
% 9.78/3.69  tff(c_1004, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_975, c_96])).
% 9.78/3.69  tff(c_1007, plain, $false, inference(negUnitSimplification, [status(thm)], [c_250, c_1004])).
% 9.78/3.69  tff(c_1009, plain, (v1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_233])).
% 9.78/3.69  tff(c_13104, plain, (![A_1867, A_1868]: (A_1867='#skF_3' | ~v1_funct_2(A_1867, A_1868, '#skF_3') | A_1868='#skF_3' | ~r1_tarski(A_1867, k2_zfmisc_1(A_1868, '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_12848, c_12848, c_12848, c_12848, c_3824])).
% 9.78/3.69  tff(c_13127, plain, ('#skF_5'='#skF_3' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_66, c_13104])).
% 9.78/3.69  tff(c_13136, plain, ('#skF_5'='#skF_3' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_13127])).
% 9.78/3.69  tff(c_13137, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_13136])).
% 9.78/3.69  tff(c_12849, plain, (k1_relat_1('#skF_5')!='#skF_2'), inference(splitRight, [status(thm)], [c_12657])).
% 9.78/3.69  tff(c_13138, plain, (k1_relat_1('#skF_5')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_13137, c_12849])).
% 9.78/3.69  tff(c_13148, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_13137, c_52])).
% 9.78/3.69  tff(c_13144, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_13137, c_117])).
% 9.78/3.69  tff(c_13146, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_13137, c_66])).
% 9.78/3.69  tff(c_12532, plain, (![B_1791, C_1792]: (k1_relset_1(k1_xboole_0, B_1791, C_1792)=k1_xboole_0 | ~v1_funct_2(C_1792, k1_xboole_0, B_1791) | ~m1_subset_1(C_1792, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_1791))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.78/3.69  tff(c_12554, plain, (![B_1791, A_6]: (k1_relset_1(k1_xboole_0, B_1791, A_6)=k1_xboole_0 | ~v1_funct_2(A_6, k1_xboole_0, B_1791) | ~r1_tarski(A_6, k2_zfmisc_1(k1_xboole_0, B_1791)))), inference(resolution, [status(thm)], [c_8, c_12532])).
% 9.78/3.69  tff(c_13386, plain, (![B_1891, A_1892]: (k1_relset_1('#skF_3', B_1891, A_1892)='#skF_3' | ~v1_funct_2(A_1892, '#skF_3', B_1891) | ~r1_tarski(A_1892, k2_zfmisc_1('#skF_3', B_1891)))), inference(demodulation, [status(thm), theory('equality')], [c_12848, c_12848, c_12848, c_12848, c_12554])).
% 9.78/3.69  tff(c_13393, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_13146, c_13386])).
% 9.78/3.69  tff(c_13417, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_13148, c_13144, c_13393])).
% 9.78/3.69  tff(c_13419, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13138, c_13417])).
% 9.78/3.69  tff(c_13420, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_13136])).
% 9.78/3.69  tff(c_13436, plain, (v1_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_13420, c_54])).
% 9.78/3.69  tff(c_149, plain, (![A_71, B_72, C_73]: (r2_hidden('#skF_1'(A_71, B_72, C_73), B_72) | ~r2_hidden(A_71, k9_relat_1(C_73, B_72)) | ~v1_relat_1(C_73))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.78/3.69  tff(c_156, plain, (![A_71, B_72, C_73, A_2]: (r2_hidden('#skF_1'(A_71, B_72, C_73), A_2) | ~m1_subset_1(B_72, k1_zfmisc_1(A_2)) | ~r2_hidden(A_71, k9_relat_1(C_73, B_72)) | ~v1_relat_1(C_73))), inference(resolution, [status(thm)], [c_149, c_4])).
% 9.78/3.69  tff(c_13952, plain, (![A_1977, B_1978, C_1979, A_1980]: (r2_hidden('#skF_1'(A_1977, B_1978, C_1979), A_1980) | ~m1_subset_1(B_1978, k1_zfmisc_1(A_1980)) | ~r2_hidden(A_1977, k9_relat_1(C_1979, B_1978)) | ~v1_relat_1(C_1979))), inference(resolution, [status(thm)], [c_149, c_4])).
% 9.78/3.69  tff(c_13432, plain, (![F_40]: (k1_funct_1('#skF_3', F_40)!='#skF_6' | ~r2_hidden(F_40, '#skF_4') | ~r2_hidden(F_40, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_13420, c_46])).
% 9.78/3.69  tff(c_14014, plain, (![A_1986, B_1987, C_1988]: (k1_funct_1('#skF_3', '#skF_1'(A_1986, B_1987, C_1988))!='#skF_6' | ~r2_hidden('#skF_1'(A_1986, B_1987, C_1988), '#skF_4') | ~m1_subset_1(B_1987, k1_zfmisc_1('#skF_2')) | ~r2_hidden(A_1986, k9_relat_1(C_1988, B_1987)) | ~v1_relat_1(C_1988))), inference(resolution, [status(thm)], [c_13952, c_13432])).
% 9.78/3.69  tff(c_15866, plain, (![A_2237, B_2238, C_2239]: (k1_funct_1('#skF_3', '#skF_1'(A_2237, B_2238, C_2239))!='#skF_6' | ~m1_subset_1(B_2238, k1_zfmisc_1('#skF_2')) | ~m1_subset_1(B_2238, k1_zfmisc_1('#skF_4')) | ~r2_hidden(A_2237, k9_relat_1(C_2239, B_2238)) | ~v1_relat_1(C_2239))), inference(resolution, [status(thm)], [c_156, c_14014])).
% 9.78/3.69  tff(c_15976, plain, (![B_2240, C_2241]: (k1_funct_1('#skF_3', '#skF_1'('#skF_6', B_2240, C_2241))!='#skF_6' | ~m1_subset_1(B_2240, k1_zfmisc_1('#skF_2')) | ~m1_subset_1(B_2240, k1_zfmisc_1('#skF_4')) | ~v1_relat_1(C_2241))), inference(resolution, [status(thm)], [c_7006, c_15866])).
% 9.78/3.69  tff(c_15979, plain, (![B_1803]: (~m1_subset_1(B_1803, k1_zfmisc_1('#skF_2')) | ~m1_subset_1(B_1803, k1_zfmisc_1('#skF_4')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_12615, c_15976])).
% 9.78/3.69  tff(c_15983, plain, (![B_2242]: (~m1_subset_1(B_2242, k1_zfmisc_1('#skF_2')) | ~m1_subset_1(B_2242, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1009, c_13436, c_15979])).
% 9.78/3.69  tff(c_15987, plain, (![D_2193, D_2195, D_2194, D_2196]: (~m1_subset_1(k9_relat_1(k9_relat_1(k9_relat_1(k9_relat_1('#skF_3', D_2193), D_2195), D_2194), D_2196), k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_15614, c_15983])).
% 9.78/3.69  tff(c_16011, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15614, c_15987])).
% 9.78/3.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.78/3.69  
% 9.78/3.69  Inference rules
% 9.78/3.69  ----------------------
% 9.78/3.69  #Ref     : 0
% 9.78/3.69  #Sup     : 3072
% 9.78/3.69  #Fact    : 0
% 9.78/3.69  #Define  : 0
% 9.78/3.69  #Split   : 89
% 9.78/3.69  #Chain   : 0
% 9.78/3.69  #Close   : 0
% 9.78/3.69  
% 9.78/3.69  Ordering : KBO
% 9.78/3.69  
% 9.78/3.69  Simplification rules
% 9.78/3.69  ----------------------
% 9.78/3.69  #Subsume      : 756
% 9.78/3.69  #Demod        : 2437
% 9.78/3.69  #Tautology    : 865
% 9.78/3.69  #SimpNegUnit  : 165
% 9.78/3.69  #BackRed      : 529
% 9.78/3.69  
% 9.78/3.69  #Partial instantiations: 0
% 9.78/3.69  #Strategies tried      : 1
% 9.78/3.69  
% 9.78/3.69  Timing (in seconds)
% 9.78/3.69  ----------------------
% 9.78/3.69  Preprocessing        : 0.34
% 9.78/3.69  Parsing              : 0.18
% 9.78/3.69  CNF conversion       : 0.02
% 9.78/3.69  Main loop            : 2.60
% 9.78/3.69  Inferencing          : 0.87
% 9.78/3.69  Reduction            : 0.84
% 9.78/3.69  Demodulation         : 0.60
% 9.78/3.69  BG Simplification    : 0.10
% 9.78/3.69  Subsumption          : 0.55
% 9.78/3.69  Abstraction          : 0.13
% 9.78/3.69  MUC search           : 0.00
% 9.78/3.69  Cooper               : 0.00
% 9.78/3.69  Total                : 3.01
% 9.78/3.69  Index Insertion      : 0.00
% 9.78/3.69  Index Deletion       : 0.00
% 9.78/3.70  Index Matching       : 0.00
% 9.78/3.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
