%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:37 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 194 expanded)
%              Number of leaves         :   36 (  81 expanded)
%              Depth                    :    8
%              Number of atoms          :  135 ( 473 expanded)
%              Number of equality atoms :   31 (  94 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_116,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ( m1_subset_1(F,A)
                 => ~ ( r2_hidden(F,C)
                      & E = k1_funct_1(D,F) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_97,axiom,(
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

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_105,plain,(
    ! [A_70,B_71,C_72,D_73] :
      ( k7_relset_1(A_70,B_71,C_72,D_73) = k9_relat_1(C_72,D_73)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_108,plain,(
    ! [D_73] : k7_relset_1('#skF_2','#skF_3','#skF_5',D_73) = k9_relat_1('#skF_5',D_73) ),
    inference(resolution,[status(thm)],[c_48,c_105])).

tff(c_120,plain,(
    ! [A_75,B_76,C_77,D_78] :
      ( m1_subset_1(k7_relset_1(A_75,B_76,C_77,D_78),k1_zfmisc_1(B_76))
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_139,plain,(
    ! [D_73] :
      ( m1_subset_1(k9_relat_1('#skF_5',D_73),k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_120])).

tff(c_157,plain,(
    ! [D_79] : m1_subset_1(k9_relat_1('#skF_5',D_79),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_139])).

tff(c_6,plain,(
    ! [C_5,B_4,A_3] :
      ( ~ v1_xboole_0(C_5)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(C_5))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_163,plain,(
    ! [A_3,D_79] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_3,k9_relat_1('#skF_5',D_79)) ) ),
    inference(resolution,[status(thm)],[c_157,c_6])).

tff(c_178,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_163])).

tff(c_10,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_59,plain,(
    ! [B_43,A_44] :
      ( v1_relat_1(B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_44))
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_62,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_59])).

tff(c_65,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_62])).

tff(c_46,plain,(
    r2_hidden('#skF_6',k7_relset_1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_110,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_46])).

tff(c_84,plain,(
    ! [A_59,B_60,C_61] :
      ( r2_hidden('#skF_1'(A_59,B_60,C_61),B_60)
      | ~ r2_hidden(A_59,k9_relat_1(C_61,B_60))
      | ~ v1_relat_1(C_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_44,plain,(
    ! [F_38] :
      ( k1_funct_1('#skF_5',F_38) != '#skF_6'
      | ~ r2_hidden(F_38,'#skF_4')
      | ~ m1_subset_1(F_38,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_165,plain,(
    ! [A_80,C_81] :
      ( k1_funct_1('#skF_5','#skF_1'(A_80,'#skF_4',C_81)) != '#skF_6'
      | ~ m1_subset_1('#skF_1'(A_80,'#skF_4',C_81),'#skF_2')
      | ~ r2_hidden(A_80,k9_relat_1(C_81,'#skF_4'))
      | ~ v1_relat_1(C_81) ) ),
    inference(resolution,[status(thm)],[c_84,c_44])).

tff(c_168,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6'
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_110,c_165])).

tff(c_175,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6'
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_168])).

tff(c_206,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_175])).

tff(c_50,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_73,plain,(
    ! [A_50,B_51,C_52] :
      ( k1_relset_1(A_50,B_51,C_52) = k1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_77,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_73])).

tff(c_258,plain,(
    ! [B_98,A_99,C_100] :
      ( k1_xboole_0 = B_98
      | k1_relset_1(A_99,B_98,C_100) = A_99
      | ~ v1_funct_2(C_100,A_99,B_98)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_99,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_265,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_258])).

tff(c_269,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_77,c_265])).

tff(c_270,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_269])).

tff(c_99,plain,(
    ! [A_65,B_66,C_67] :
      ( r2_hidden('#skF_1'(A_65,B_66,C_67),k1_relat_1(C_67))
      | ~ r2_hidden(A_65,k9_relat_1(C_67,B_66))
      | ~ v1_relat_1(C_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_103,plain,(
    ! [A_65,B_66,C_67] :
      ( m1_subset_1('#skF_1'(A_65,B_66,C_67),k1_relat_1(C_67))
      | ~ r2_hidden(A_65,k9_relat_1(C_67,B_66))
      | ~ v1_relat_1(C_67) ) ),
    inference(resolution,[status(thm)],[c_99,c_4])).

tff(c_275,plain,(
    ! [A_65,B_66] :
      ( m1_subset_1('#skF_1'(A_65,B_66,'#skF_5'),'#skF_2')
      | ~ r2_hidden(A_65,k9_relat_1('#skF_5',B_66))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_103])).

tff(c_291,plain,(
    ! [A_104,B_105] :
      ( m1_subset_1('#skF_1'(A_104,B_105,'#skF_5'),'#skF_2')
      | ~ r2_hidden(A_104,k9_relat_1('#skF_5',B_105)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_275])).

tff(c_302,plain,(
    m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_110,c_291])).

tff(c_312,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_206,c_302])).

tff(c_313,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_269])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_320,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_2])).

tff(c_322,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_320])).

tff(c_323,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_175])).

tff(c_52,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_179,plain,(
    ! [A_82,B_83,C_84] :
      ( r2_hidden(k4_tarski('#skF_1'(A_82,B_83,C_84),A_82),C_84)
      | ~ r2_hidden(A_82,k9_relat_1(C_84,B_83))
      | ~ v1_relat_1(C_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_22,plain,(
    ! [C_19,A_17,B_18] :
      ( k1_funct_1(C_19,A_17) = B_18
      | ~ r2_hidden(k4_tarski(A_17,B_18),C_19)
      | ~ v1_funct_1(C_19)
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_469,plain,(
    ! [C_129,A_130,B_131] :
      ( k1_funct_1(C_129,'#skF_1'(A_130,B_131,C_129)) = A_130
      | ~ v1_funct_1(C_129)
      | ~ r2_hidden(A_130,k9_relat_1(C_129,B_131))
      | ~ v1_relat_1(C_129) ) ),
    inference(resolution,[status(thm)],[c_179,c_22])).

tff(c_477,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_110,c_469])).

tff(c_485,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_52,c_477])).

tff(c_487,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_323,c_485])).

tff(c_488,plain,(
    ! [A_3,D_79] : ~ r2_hidden(A_3,k9_relat_1('#skF_5',D_79)) ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_518,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_488,c_110])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:10:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.41  
% 2.71/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.42  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 2.71/1.42  
% 2.71/1.42  %Foreground sorts:
% 2.71/1.42  
% 2.71/1.42  
% 2.71/1.42  %Background operators:
% 2.71/1.42  
% 2.71/1.42  
% 2.71/1.42  %Foreground operators:
% 2.71/1.42  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.71/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.71/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.71/1.42  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.71/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.71/1.42  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.71/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.71/1.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.71/1.42  tff('#skF_6', type, '#skF_6': $i).
% 2.71/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.71/1.42  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.71/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.71/1.42  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.71/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.71/1.42  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.71/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.71/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.71/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.71/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.71/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.71/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.71/1.42  
% 2.97/1.43  tff(f_116, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_funct_2)).
% 2.97/1.43  tff(f_79, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.97/1.43  tff(f_71, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 2.97/1.43  tff(f_37, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.97/1.43  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.97/1.43  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.97/1.43  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 2.97/1.43  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.97/1.43  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.97/1.43  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.97/1.43  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.97/1.43  tff(f_67, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 2.97/1.43  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.97/1.43  tff(c_105, plain, (![A_70, B_71, C_72, D_73]: (k7_relset_1(A_70, B_71, C_72, D_73)=k9_relat_1(C_72, D_73) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.97/1.43  tff(c_108, plain, (![D_73]: (k7_relset_1('#skF_2', '#skF_3', '#skF_5', D_73)=k9_relat_1('#skF_5', D_73))), inference(resolution, [status(thm)], [c_48, c_105])).
% 2.97/1.43  tff(c_120, plain, (![A_75, B_76, C_77, D_78]: (m1_subset_1(k7_relset_1(A_75, B_76, C_77, D_78), k1_zfmisc_1(B_76)) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.97/1.43  tff(c_139, plain, (![D_73]: (m1_subset_1(k9_relat_1('#skF_5', D_73), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_108, c_120])).
% 2.97/1.43  tff(c_157, plain, (![D_79]: (m1_subset_1(k9_relat_1('#skF_5', D_79), k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_139])).
% 2.97/1.43  tff(c_6, plain, (![C_5, B_4, A_3]: (~v1_xboole_0(C_5) | ~m1_subset_1(B_4, k1_zfmisc_1(C_5)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.97/1.43  tff(c_163, plain, (![A_3, D_79]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_3, k9_relat_1('#skF_5', D_79)))), inference(resolution, [status(thm)], [c_157, c_6])).
% 2.97/1.43  tff(c_178, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_163])).
% 2.97/1.43  tff(c_10, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.97/1.43  tff(c_59, plain, (![B_43, A_44]: (v1_relat_1(B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(A_44)) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.97/1.43  tff(c_62, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_48, c_59])).
% 2.97/1.43  tff(c_65, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_62])).
% 2.97/1.43  tff(c_46, plain, (r2_hidden('#skF_6', k7_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.97/1.43  tff(c_110, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_46])).
% 2.97/1.43  tff(c_84, plain, (![A_59, B_60, C_61]: (r2_hidden('#skF_1'(A_59, B_60, C_61), B_60) | ~r2_hidden(A_59, k9_relat_1(C_61, B_60)) | ~v1_relat_1(C_61))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.97/1.43  tff(c_44, plain, (![F_38]: (k1_funct_1('#skF_5', F_38)!='#skF_6' | ~r2_hidden(F_38, '#skF_4') | ~m1_subset_1(F_38, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.97/1.43  tff(c_165, plain, (![A_80, C_81]: (k1_funct_1('#skF_5', '#skF_1'(A_80, '#skF_4', C_81))!='#skF_6' | ~m1_subset_1('#skF_1'(A_80, '#skF_4', C_81), '#skF_2') | ~r2_hidden(A_80, k9_relat_1(C_81, '#skF_4')) | ~v1_relat_1(C_81))), inference(resolution, [status(thm)], [c_84, c_44])).
% 2.97/1.43  tff(c_168, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6' | ~m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_110, c_165])).
% 2.97/1.43  tff(c_175, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6' | ~m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_168])).
% 2.97/1.43  tff(c_206, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2')), inference(splitLeft, [status(thm)], [c_175])).
% 2.97/1.43  tff(c_50, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.97/1.43  tff(c_73, plain, (![A_50, B_51, C_52]: (k1_relset_1(A_50, B_51, C_52)=k1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.97/1.43  tff(c_77, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_73])).
% 2.97/1.43  tff(c_258, plain, (![B_98, A_99, C_100]: (k1_xboole_0=B_98 | k1_relset_1(A_99, B_98, C_100)=A_99 | ~v1_funct_2(C_100, A_99, B_98) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_99, B_98))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.97/1.43  tff(c_265, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_258])).
% 2.97/1.43  tff(c_269, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_77, c_265])).
% 2.97/1.43  tff(c_270, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(splitLeft, [status(thm)], [c_269])).
% 2.97/1.43  tff(c_99, plain, (![A_65, B_66, C_67]: (r2_hidden('#skF_1'(A_65, B_66, C_67), k1_relat_1(C_67)) | ~r2_hidden(A_65, k9_relat_1(C_67, B_66)) | ~v1_relat_1(C_67))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.97/1.43  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.97/1.43  tff(c_103, plain, (![A_65, B_66, C_67]: (m1_subset_1('#skF_1'(A_65, B_66, C_67), k1_relat_1(C_67)) | ~r2_hidden(A_65, k9_relat_1(C_67, B_66)) | ~v1_relat_1(C_67))), inference(resolution, [status(thm)], [c_99, c_4])).
% 2.97/1.43  tff(c_275, plain, (![A_65, B_66]: (m1_subset_1('#skF_1'(A_65, B_66, '#skF_5'), '#skF_2') | ~r2_hidden(A_65, k9_relat_1('#skF_5', B_66)) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_270, c_103])).
% 2.97/1.43  tff(c_291, plain, (![A_104, B_105]: (m1_subset_1('#skF_1'(A_104, B_105, '#skF_5'), '#skF_2') | ~r2_hidden(A_104, k9_relat_1('#skF_5', B_105)))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_275])).
% 2.97/1.43  tff(c_302, plain, (m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2')), inference(resolution, [status(thm)], [c_110, c_291])).
% 2.97/1.43  tff(c_312, plain, $false, inference(negUnitSimplification, [status(thm)], [c_206, c_302])).
% 2.97/1.43  tff(c_313, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_269])).
% 2.97/1.43  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.97/1.43  tff(c_320, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_313, c_2])).
% 2.97/1.43  tff(c_322, plain, $false, inference(negUnitSimplification, [status(thm)], [c_178, c_320])).
% 2.97/1.43  tff(c_323, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6'), inference(splitRight, [status(thm)], [c_175])).
% 2.97/1.43  tff(c_52, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.97/1.43  tff(c_179, plain, (![A_82, B_83, C_84]: (r2_hidden(k4_tarski('#skF_1'(A_82, B_83, C_84), A_82), C_84) | ~r2_hidden(A_82, k9_relat_1(C_84, B_83)) | ~v1_relat_1(C_84))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.97/1.43  tff(c_22, plain, (![C_19, A_17, B_18]: (k1_funct_1(C_19, A_17)=B_18 | ~r2_hidden(k4_tarski(A_17, B_18), C_19) | ~v1_funct_1(C_19) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.97/1.43  tff(c_469, plain, (![C_129, A_130, B_131]: (k1_funct_1(C_129, '#skF_1'(A_130, B_131, C_129))=A_130 | ~v1_funct_1(C_129) | ~r2_hidden(A_130, k9_relat_1(C_129, B_131)) | ~v1_relat_1(C_129))), inference(resolution, [status(thm)], [c_179, c_22])).
% 2.97/1.43  tff(c_477, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_110, c_469])).
% 2.97/1.43  tff(c_485, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_65, c_52, c_477])).
% 2.97/1.43  tff(c_487, plain, $false, inference(negUnitSimplification, [status(thm)], [c_323, c_485])).
% 2.97/1.43  tff(c_488, plain, (![A_3, D_79]: (~r2_hidden(A_3, k9_relat_1('#skF_5', D_79)))), inference(splitRight, [status(thm)], [c_163])).
% 2.97/1.43  tff(c_518, plain, $false, inference(negUnitSimplification, [status(thm)], [c_488, c_110])).
% 2.97/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.43  
% 2.97/1.43  Inference rules
% 2.97/1.43  ----------------------
% 2.97/1.43  #Ref     : 0
% 2.97/1.43  #Sup     : 93
% 2.97/1.43  #Fact    : 0
% 2.97/1.43  #Define  : 0
% 2.97/1.43  #Split   : 7
% 2.97/1.43  #Chain   : 0
% 2.97/1.43  #Close   : 0
% 2.97/1.43  
% 2.97/1.43  Ordering : KBO
% 2.97/1.43  
% 2.97/1.43  Simplification rules
% 2.97/1.43  ----------------------
% 2.97/1.43  #Subsume      : 6
% 2.97/1.43  #Demod        : 36
% 2.97/1.43  #Tautology    : 13
% 2.97/1.43  #SimpNegUnit  : 4
% 2.97/1.43  #BackRed      : 10
% 2.97/1.43  
% 2.97/1.43  #Partial instantiations: 0
% 2.97/1.43  #Strategies tried      : 1
% 2.97/1.43  
% 2.97/1.43  Timing (in seconds)
% 2.97/1.43  ----------------------
% 2.97/1.44  Preprocessing        : 0.33
% 2.97/1.44  Parsing              : 0.17
% 2.97/1.44  CNF conversion       : 0.02
% 2.97/1.44  Main loop            : 0.32
% 2.97/1.44  Inferencing          : 0.12
% 2.97/1.44  Reduction            : 0.10
% 2.97/1.44  Demodulation         : 0.07
% 2.97/1.44  BG Simplification    : 0.02
% 2.97/1.44  Subsumption          : 0.06
% 2.97/1.44  Abstraction          : 0.02
% 2.97/1.44  MUC search           : 0.00
% 2.97/1.44  Cooper               : 0.00
% 2.97/1.44  Total                : 0.70
% 2.97/1.44  Index Insertion      : 0.00
% 2.97/1.44  Index Deletion       : 0.00
% 2.97/1.44  Index Matching       : 0.00
% 2.97/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
