%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:56 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 236 expanded)
%              Number of leaves         :   20 (  86 expanded)
%              Depth                    :    7
%              Number of atoms          :  157 ( 962 expanded)
%              Number of equality atoms :   24 ( 239 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_partfun1 > m1_subset_1 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( r1_partfun1(C,D)
             => ( ( B = k1_xboole_0
                  & A != k1_xboole_0 )
                | r2_relset_1(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( v1_partfun1(C,A)
              & v1_partfun1(D,A)
              & r1_partfun1(C,D) )
           => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).

tff(c_16,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_44,plain,(
    ! [A_19,B_20,C_21,D_22] :
      ( r2_relset_1(A_19,B_20,C_21,C_21)
      | ~ m1_subset_1(D_22,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20)))
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_57,plain,(
    ! [C_27] :
      ( r2_relset_1('#skF_1','#skF_2',C_27,C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_16,c_44])).

tff(c_62,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_57])).

tff(c_12,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_27,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_12])).

tff(c_26,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_24,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_29,plain,(
    ! [B_16,C_17,A_18] :
      ( k1_xboole_0 = B_16
      | v1_partfun1(C_17,A_18)
      | ~ v1_funct_2(C_17,A_18,B_16)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_18,B_16)))
      | ~ v1_funct_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_35,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_29])).

tff(c_42,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_partfun1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_35])).

tff(c_43,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_27,c_42])).

tff(c_20,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_18,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_32,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_partfun1('#skF_4','#skF_1')
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_29])).

tff(c_38,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_partfun1('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_32])).

tff(c_39,plain,(
    v1_partfun1('#skF_4','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_27,c_38])).

tff(c_14,plain,(
    r1_partfun1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_51,plain,(
    ! [D_23,C_24,A_25,B_26] :
      ( D_23 = C_24
      | ~ r1_partfun1(C_24,D_23)
      | ~ v1_partfun1(D_23,A_25)
      | ~ v1_partfun1(C_24,A_25)
      | ~ m1_subset_1(D_23,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_funct_1(D_23)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_funct_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_53,plain,(
    ! [A_25,B_26] :
      ( '#skF_3' = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_25)
      | ~ v1_partfun1('#skF_3',A_25)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_14,c_51])).

tff(c_56,plain,(
    ! [A_25,B_26] :
      ( '#skF_3' = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_25)
      | ~ v1_partfun1('#skF_3',A_25)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_20,c_53])).

tff(c_65,plain,(
    ! [A_28,B_29] :
      ( ~ v1_partfun1('#skF_4',A_28)
      | ~ v1_partfun1('#skF_3',A_28)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_68,plain,
    ( ~ v1_partfun1('#skF_4','#skF_1')
    | ~ v1_partfun1('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_22,c_65])).

tff(c_72,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_43,c_39,c_68])).

tff(c_73,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_10,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_77,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_10])).

tff(c_86,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_77])).

tff(c_87,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_88,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_93,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_88])).

tff(c_102,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_16])).

tff(c_133,plain,(
    ! [A_35,B_36,C_37,D_38] :
      ( r2_relset_1(A_35,B_36,C_37,C_37)
      | ~ m1_subset_1(D_38,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36)))
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_146,plain,(
    ! [C_43] :
      ( r2_relset_1('#skF_1','#skF_1',C_43,C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_102,c_133])).

tff(c_151,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_102,c_146])).

tff(c_94,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_24])).

tff(c_101,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_22])).

tff(c_4,plain,(
    ! [C_7,B_6] :
      ( v1_partfun1(C_7,k1_xboole_0)
      | ~ v1_funct_2(C_7,k1_xboole_0,B_6)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_6)))
      | ~ v1_funct_1(C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_104,plain,(
    ! [C_30,B_31] :
      ( v1_partfun1(C_30,'#skF_1')
      | ~ v1_funct_2(C_30,'#skF_1',B_31)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_31)))
      | ~ v1_funct_1(C_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_87,c_87,c_4])).

tff(c_110,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_101,c_104])).

tff(c_116,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_94,c_110])).

tff(c_99,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_18])).

tff(c_107,plain,
    ( v1_partfun1('#skF_4','#skF_1')
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_102,c_104])).

tff(c_113,plain,(
    v1_partfun1('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_99,c_107])).

tff(c_140,plain,(
    ! [D_39,C_40,A_41,B_42] :
      ( D_39 = C_40
      | ~ r1_partfun1(C_40,D_39)
      | ~ v1_partfun1(D_39,A_41)
      | ~ v1_partfun1(C_40,A_41)
      | ~ m1_subset_1(D_39,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42)))
      | ~ v1_funct_1(D_39)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42)))
      | ~ v1_funct_1(C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_142,plain,(
    ! [A_41,B_42] :
      ( '#skF_3' = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_41)
      | ~ v1_partfun1('#skF_3',A_41)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_41,B_42)))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_41,B_42)))
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_14,c_140])).

tff(c_145,plain,(
    ! [A_41,B_42] :
      ( '#skF_3' = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_41)
      | ~ v1_partfun1('#skF_3',A_41)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_41,B_42)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_20,c_142])).

tff(c_154,plain,(
    ! [A_44,B_45] :
      ( ~ v1_partfun1('#skF_4',A_44)
      | ~ v1_partfun1('#skF_3',A_44)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_44,B_45)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(splitLeft,[status(thm)],[c_145])).

tff(c_157,plain,
    ( ~ v1_partfun1('#skF_4','#skF_1')
    | ~ v1_partfun1('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_101,c_154])).

tff(c_161,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_116,c_113,c_157])).

tff(c_162,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_100,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_10])).

tff(c_166,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_100])).

tff(c_175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_166])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:04:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.23  
% 2.07/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.23  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_partfun1 > m1_subset_1 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.07/1.23  
% 2.07/1.23  %Foreground sorts:
% 2.07/1.23  
% 2.07/1.23  
% 2.07/1.23  %Background operators:
% 2.07/1.23  
% 2.07/1.23  
% 2.07/1.23  %Foreground operators:
% 2.07/1.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.07/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.23  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.07/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.07/1.23  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.07/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.07/1.23  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.07/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.07/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.07/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.07/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.07/1.23  tff('#skF_4', type, '#skF_4': $i).
% 2.07/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.23  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 2.07/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.07/1.23  
% 2.07/1.25  tff(f_88, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_2)).
% 2.07/1.25  tff(f_31, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.07/1.25  tff(f_48, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_funct_2)).
% 2.07/1.25  tff(f_65, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_partfun1)).
% 2.07/1.25  tff(c_16, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.07/1.25  tff(c_44, plain, (![A_19, B_20, C_21, D_22]: (r2_relset_1(A_19, B_20, C_21, C_21) | ~m1_subset_1(D_22, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.07/1.25  tff(c_57, plain, (![C_27]: (r2_relset_1('#skF_1', '#skF_2', C_27, C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_16, c_44])).
% 2.07/1.25  tff(c_62, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_16, c_57])).
% 2.07/1.25  tff(c_12, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.07/1.25  tff(c_27, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_12])).
% 2.07/1.25  tff(c_26, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.07/1.25  tff(c_24, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.07/1.25  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.07/1.25  tff(c_29, plain, (![B_16, C_17, A_18]: (k1_xboole_0=B_16 | v1_partfun1(C_17, A_18) | ~v1_funct_2(C_17, A_18, B_16) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_18, B_16))) | ~v1_funct_1(C_17))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.07/1.25  tff(c_35, plain, (k1_xboole_0='#skF_2' | v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_29])).
% 2.07/1.25  tff(c_42, plain, (k1_xboole_0='#skF_2' | v1_partfun1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_35])).
% 2.07/1.25  tff(c_43, plain, (v1_partfun1('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_27, c_42])).
% 2.07/1.25  tff(c_20, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.07/1.25  tff(c_18, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.07/1.25  tff(c_32, plain, (k1_xboole_0='#skF_2' | v1_partfun1('#skF_4', '#skF_1') | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_29])).
% 2.07/1.25  tff(c_38, plain, (k1_xboole_0='#skF_2' | v1_partfun1('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_32])).
% 2.07/1.25  tff(c_39, plain, (v1_partfun1('#skF_4', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_27, c_38])).
% 2.07/1.25  tff(c_14, plain, (r1_partfun1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.07/1.25  tff(c_51, plain, (![D_23, C_24, A_25, B_26]: (D_23=C_24 | ~r1_partfun1(C_24, D_23) | ~v1_partfun1(D_23, A_25) | ~v1_partfun1(C_24, A_25) | ~m1_subset_1(D_23, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_funct_1(D_23) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_funct_1(C_24))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.07/1.25  tff(c_53, plain, (![A_25, B_26]: ('#skF_3'='#skF_4' | ~v1_partfun1('#skF_4', A_25) | ~v1_partfun1('#skF_3', A_25) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_14, c_51])).
% 2.07/1.25  tff(c_56, plain, (![A_25, B_26]: ('#skF_3'='#skF_4' | ~v1_partfun1('#skF_4', A_25) | ~v1_partfun1('#skF_3', A_25) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_20, c_53])).
% 2.07/1.25  tff(c_65, plain, (![A_28, B_29]: (~v1_partfun1('#skF_4', A_28) | ~v1_partfun1('#skF_3', A_28) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(splitLeft, [status(thm)], [c_56])).
% 2.07/1.25  tff(c_68, plain, (~v1_partfun1('#skF_4', '#skF_1') | ~v1_partfun1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_22, c_65])).
% 2.07/1.25  tff(c_72, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_43, c_39, c_68])).
% 2.07/1.25  tff(c_73, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_56])).
% 2.07/1.25  tff(c_10, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.07/1.25  tff(c_77, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_10])).
% 2.07/1.25  tff(c_86, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_77])).
% 2.07/1.25  tff(c_87, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_12])).
% 2.07/1.25  tff(c_88, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_12])).
% 2.07/1.25  tff(c_93, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_87, c_88])).
% 2.07/1.25  tff(c_102, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_16])).
% 2.07/1.25  tff(c_133, plain, (![A_35, B_36, C_37, D_38]: (r2_relset_1(A_35, B_36, C_37, C_37) | ~m1_subset_1(D_38, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.07/1.25  tff(c_146, plain, (![C_43]: (r2_relset_1('#skF_1', '#skF_1', C_43, C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))))), inference(resolution, [status(thm)], [c_102, c_133])).
% 2.07/1.25  tff(c_151, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_102, c_146])).
% 2.07/1.25  tff(c_94, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_24])).
% 2.07/1.25  tff(c_101, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_22])).
% 2.07/1.25  tff(c_4, plain, (![C_7, B_6]: (v1_partfun1(C_7, k1_xboole_0) | ~v1_funct_2(C_7, k1_xboole_0, B_6) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_6))) | ~v1_funct_1(C_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.07/1.25  tff(c_104, plain, (![C_30, B_31]: (v1_partfun1(C_30, '#skF_1') | ~v1_funct_2(C_30, '#skF_1', B_31) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_31))) | ~v1_funct_1(C_30))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_87, c_87, c_4])).
% 2.07/1.25  tff(c_110, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_101, c_104])).
% 2.07/1.25  tff(c_116, plain, (v1_partfun1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_94, c_110])).
% 2.07/1.25  tff(c_99, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_18])).
% 2.07/1.25  tff(c_107, plain, (v1_partfun1('#skF_4', '#skF_1') | ~v1_funct_2('#skF_4', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_102, c_104])).
% 2.07/1.25  tff(c_113, plain, (v1_partfun1('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_99, c_107])).
% 2.07/1.25  tff(c_140, plain, (![D_39, C_40, A_41, B_42]: (D_39=C_40 | ~r1_partfun1(C_40, D_39) | ~v1_partfun1(D_39, A_41) | ~v1_partfun1(C_40, A_41) | ~m1_subset_1(D_39, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))) | ~v1_funct_1(D_39) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))) | ~v1_funct_1(C_40))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.07/1.25  tff(c_142, plain, (![A_41, B_42]: ('#skF_3'='#skF_4' | ~v1_partfun1('#skF_4', A_41) | ~v1_partfun1('#skF_3', A_41) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_14, c_140])).
% 2.07/1.25  tff(c_145, plain, (![A_41, B_42]: ('#skF_3'='#skF_4' | ~v1_partfun1('#skF_4', A_41) | ~v1_partfun1('#skF_3', A_41) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_20, c_142])).
% 2.07/1.25  tff(c_154, plain, (![A_44, B_45]: (~v1_partfun1('#skF_4', A_44) | ~v1_partfun1('#skF_3', A_44) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(splitLeft, [status(thm)], [c_145])).
% 2.07/1.25  tff(c_157, plain, (~v1_partfun1('#skF_4', '#skF_1') | ~v1_partfun1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_101, c_154])).
% 2.07/1.25  tff(c_161, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_116, c_113, c_157])).
% 2.07/1.25  tff(c_162, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_145])).
% 2.07/1.25  tff(c_100, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_10])).
% 2.07/1.25  tff(c_166, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_162, c_100])).
% 2.07/1.25  tff(c_175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_151, c_166])).
% 2.07/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.25  
% 2.07/1.25  Inference rules
% 2.07/1.25  ----------------------
% 2.07/1.25  #Ref     : 0
% 2.07/1.25  #Sup     : 22
% 2.07/1.25  #Fact    : 0
% 2.07/1.25  #Define  : 0
% 2.07/1.25  #Split   : 3
% 2.07/1.25  #Chain   : 0
% 2.07/1.25  #Close   : 0
% 2.07/1.25  
% 2.07/1.25  Ordering : KBO
% 2.07/1.25  
% 2.07/1.25  Simplification rules
% 2.07/1.25  ----------------------
% 2.07/1.25  #Subsume      : 2
% 2.07/1.25  #Demod        : 58
% 2.07/1.25  #Tautology    : 12
% 2.07/1.25  #SimpNegUnit  : 2
% 2.07/1.25  #BackRed      : 15
% 2.07/1.25  
% 2.07/1.25  #Partial instantiations: 0
% 2.07/1.25  #Strategies tried      : 1
% 2.07/1.25  
% 2.07/1.25  Timing (in seconds)
% 2.07/1.25  ----------------------
% 2.07/1.25  Preprocessing        : 0.31
% 2.07/1.25  Parsing              : 0.17
% 2.07/1.25  CNF conversion       : 0.02
% 2.07/1.25  Main loop            : 0.17
% 2.07/1.25  Inferencing          : 0.07
% 2.07/1.25  Reduction            : 0.06
% 2.07/1.25  Demodulation         : 0.04
% 2.07/1.25  BG Simplification    : 0.01
% 2.07/1.25  Subsumption          : 0.02
% 2.07/1.25  Abstraction          : 0.01
% 2.07/1.25  MUC search           : 0.00
% 2.07/1.25  Cooper               : 0.00
% 2.07/1.25  Total                : 0.52
% 2.07/1.25  Index Insertion      : 0.00
% 2.07/1.25  Index Deletion       : 0.00
% 2.07/1.25  Index Matching       : 0.00
% 2.07/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
