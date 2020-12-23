%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0643+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:38 EST 2020

% Result     : Theorem 10.52s
% Output     : CNFRefutation 10.52s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 301 expanded)
%              Number of leaves         :   35 ( 137 expanded)
%              Depth                    :   12
%              Number of atoms          :  193 (1359 expanded)
%              Number of equality atoms :   50 ( 518 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_4 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_2 > #skF_7 > #skF_1 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_123,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ( ( k1_relat_1(B) = A
                & k1_relat_1(C) = A
                & r1_tarski(k2_relat_1(C),A)
                & v2_funct_1(B)
                & k5_relat_1(C,B) = B )
             => C = k6_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_39,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_101,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

tff(c_50,plain,(
    k6_relat_1('#skF_8') != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_64,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_62,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_58,plain,(
    k1_relat_1('#skF_10') = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_10644,plain,(
    ! [B_462] :
      ( k1_funct_1(B_462,'#skF_7'(k1_relat_1(B_462),B_462)) != '#skF_7'(k1_relat_1(B_462),B_462)
      | k6_relat_1(k1_relat_1(B_462)) = B_462
      | ~ v1_funct_1(B_462)
      | ~ v1_relat_1(B_462) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_10647,plain,
    ( k1_funct_1('#skF_10','#skF_7'('#skF_8','#skF_10')) != '#skF_7'(k1_relat_1('#skF_10'),'#skF_10')
    | k6_relat_1(k1_relat_1('#skF_10')) = '#skF_10'
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_10644])).

tff(c_10652,plain,
    ( k1_funct_1('#skF_10','#skF_7'('#skF_8','#skF_10')) != '#skF_7'('#skF_8','#skF_10')
    | k6_relat_1('#skF_8') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_58,c_58,c_10647])).

tff(c_10653,plain,(
    k1_funct_1('#skF_10','#skF_7'('#skF_8','#skF_10')) != '#skF_7'('#skF_8','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_10652])).

tff(c_301,plain,(
    ! [B_112] :
      ( r2_hidden('#skF_7'(k1_relat_1(B_112),B_112),k1_relat_1(B_112))
      | k6_relat_1(k1_relat_1(B_112)) = B_112
      | ~ v1_funct_1(B_112)
      | ~ v1_relat_1(B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_309,plain,
    ( r2_hidden('#skF_7'('#skF_8','#skF_10'),k1_relat_1('#skF_10'))
    | k6_relat_1(k1_relat_1('#skF_10')) = '#skF_10'
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_301])).

tff(c_322,plain,
    ( r2_hidden('#skF_7'('#skF_8','#skF_10'),'#skF_8')
    | k6_relat_1('#skF_8') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_58,c_58,c_309])).

tff(c_323,plain,(
    r2_hidden('#skF_7'('#skF_8','#skF_10'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_322])).

tff(c_56,plain,(
    r1_tarski(k2_relat_1('#skF_10'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_290,plain,(
    ! [A_110,D_111] :
      ( r2_hidden(k1_funct_1(A_110,D_111),k2_relat_1(A_110))
      | ~ r2_hidden(D_111,k1_relat_1(A_110))
      | ~ v1_funct_1(A_110)
      | ~ v1_relat_1(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_44,plain,(
    ! [A_59,B_60] :
      ( m1_subset_1(A_59,k1_zfmisc_1(B_60))
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_93,plain,(
    ! [A_75,C_76,B_77] :
      ( m1_subset_1(A_75,C_76)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(C_76))
      | ~ r2_hidden(A_75,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_96,plain,(
    ! [A_75,B_60,A_59] :
      ( m1_subset_1(A_75,B_60)
      | ~ r2_hidden(A_75,A_59)
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(resolution,[status(thm)],[c_44,c_93])).

tff(c_11310,plain,(
    ! [A_511,D_512,B_513] :
      ( m1_subset_1(k1_funct_1(A_511,D_512),B_513)
      | ~ r1_tarski(k2_relat_1(A_511),B_513)
      | ~ r2_hidden(D_512,k1_relat_1(A_511))
      | ~ v1_funct_1(A_511)
      | ~ v1_relat_1(A_511) ) ),
    inference(resolution,[status(thm)],[c_290,c_96])).

tff(c_11312,plain,(
    ! [D_512] :
      ( m1_subset_1(k1_funct_1('#skF_10',D_512),'#skF_8')
      | ~ r2_hidden(D_512,k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_56,c_11310])).

tff(c_11315,plain,(
    ! [D_512] :
      ( m1_subset_1(k1_funct_1('#skF_10',D_512),'#skF_8')
      | ~ r2_hidden(D_512,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_58,c_11312])).

tff(c_48,plain,(
    ! [B_65,A_64] :
      ( ~ v1_xboole_0(B_65)
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_337,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_323,c_48])).

tff(c_32,plain,(
    ! [A_52,B_53] :
      ( r2_hidden(A_52,B_53)
      | v1_xboole_0(B_53)
      | ~ m1_subset_1(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_68,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_66,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_60,plain,(
    k1_relat_1('#skF_9') = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_52,plain,(
    k5_relat_1('#skF_10','#skF_9') = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_36,plain,(
    ! [B_55] :
      ( r2_hidden('#skF_7'(k1_relat_1(B_55),B_55),k1_relat_1(B_55))
      | k6_relat_1(k1_relat_1(B_55)) = B_55
      | ~ v1_funct_1(B_55)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_11039,plain,(
    ! [B_499,C_500,A_501] :
      ( k1_funct_1(k5_relat_1(B_499,C_500),A_501) = k1_funct_1(C_500,k1_funct_1(B_499,A_501))
      | ~ r2_hidden(A_501,k1_relat_1(B_499))
      | ~ v1_funct_1(C_500)
      | ~ v1_relat_1(C_500)
      | ~ v1_funct_1(B_499)
      | ~ v1_relat_1(B_499) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_13290,plain,(
    ! [B_616,C_617] :
      ( k1_funct_1(k5_relat_1(B_616,C_617),'#skF_7'(k1_relat_1(B_616),B_616)) = k1_funct_1(C_617,k1_funct_1(B_616,'#skF_7'(k1_relat_1(B_616),B_616)))
      | ~ v1_funct_1(C_617)
      | ~ v1_relat_1(C_617)
      | k6_relat_1(k1_relat_1(B_616)) = B_616
      | ~ v1_funct_1(B_616)
      | ~ v1_relat_1(B_616) ) ),
    inference(resolution,[status(thm)],[c_36,c_11039])).

tff(c_13344,plain,
    ( k1_funct_1('#skF_9',k1_funct_1('#skF_10','#skF_7'(k1_relat_1('#skF_10'),'#skF_10'))) = k1_funct_1('#skF_9','#skF_7'(k1_relat_1('#skF_10'),'#skF_10'))
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9')
    | k6_relat_1(k1_relat_1('#skF_10')) = '#skF_10'
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_13290])).

tff(c_13378,plain,
    ( k1_funct_1('#skF_9',k1_funct_1('#skF_10','#skF_7'('#skF_8','#skF_10'))) = k1_funct_1('#skF_9','#skF_7'('#skF_8','#skF_10'))
    | k6_relat_1('#skF_8') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_58,c_68,c_66,c_58,c_58,c_13344])).

tff(c_13379,plain,(
    k1_funct_1('#skF_9',k1_funct_1('#skF_10','#skF_7'('#skF_8','#skF_10'))) = k1_funct_1('#skF_9','#skF_7'('#skF_8','#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_13378])).

tff(c_2,plain,(
    ! [A_1,D_40] :
      ( r2_hidden(k1_funct_1(A_1,D_40),k2_relat_1(A_1))
      | ~ r2_hidden(D_40,k1_relat_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_13429,plain,
    ( r2_hidden(k1_funct_1('#skF_9','#skF_7'('#skF_8','#skF_10')),k2_relat_1('#skF_9'))
    | ~ r2_hidden(k1_funct_1('#skF_10','#skF_7'('#skF_8','#skF_10')),k1_relat_1('#skF_9'))
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_13379,c_2])).

tff(c_13455,plain,
    ( r2_hidden(k1_funct_1('#skF_9','#skF_7'('#skF_8','#skF_10')),k2_relat_1('#skF_9'))
    | ~ r2_hidden(k1_funct_1('#skF_10','#skF_7'('#skF_8','#skF_10')),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_60,c_13429])).

tff(c_13511,plain,(
    ~ r2_hidden(k1_funct_1('#skF_10','#skF_7'('#skF_8','#skF_10')),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_13455])).

tff(c_13514,plain,
    ( v1_xboole_0('#skF_8')
    | ~ m1_subset_1(k1_funct_1('#skF_10','#skF_7'('#skF_8','#skF_10')),'#skF_8') ),
    inference(resolution,[status(thm)],[c_32,c_13511])).

tff(c_13517,plain,(
    ~ m1_subset_1(k1_funct_1('#skF_10','#skF_7'('#skF_8','#skF_10')),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_337,c_13514])).

tff(c_13520,plain,(
    ~ r2_hidden('#skF_7'('#skF_8','#skF_10'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_11315,c_13517])).

tff(c_13524,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_13520])).

tff(c_13526,plain,(
    r2_hidden(k1_funct_1('#skF_10','#skF_7'('#skF_8','#skF_10')),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_13455])).

tff(c_54,plain,(
    v2_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_13347,plain,(
    ! [C_617] :
      ( k1_funct_1(C_617,k1_funct_1('#skF_10','#skF_7'(k1_relat_1('#skF_10'),'#skF_10'))) = k1_funct_1(k5_relat_1('#skF_10',C_617),'#skF_7'('#skF_8','#skF_10'))
      | ~ v1_funct_1(C_617)
      | ~ v1_relat_1(C_617)
      | k6_relat_1(k1_relat_1('#skF_10')) = '#skF_10'
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_13290])).

tff(c_13381,plain,(
    ! [C_617] :
      ( k1_funct_1(k5_relat_1('#skF_10',C_617),'#skF_7'('#skF_8','#skF_10')) = k1_funct_1(C_617,k1_funct_1('#skF_10','#skF_7'('#skF_8','#skF_10')))
      | ~ v1_funct_1(C_617)
      | ~ v1_relat_1(C_617)
      | k6_relat_1('#skF_8') = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_58,c_58,c_13347])).

tff(c_13462,plain,(
    ! [C_618] :
      ( k1_funct_1(k5_relat_1('#skF_10',C_618),'#skF_7'('#skF_8','#skF_10')) = k1_funct_1(C_618,k1_funct_1('#skF_10','#skF_7'('#skF_8','#skF_10')))
      | ~ v1_funct_1(C_618)
      | ~ v1_relat_1(C_618) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_13381])).

tff(c_20,plain,(
    ! [C_47,B_46,A_41] :
      ( C_47 = B_46
      | k1_funct_1(A_41,C_47) != k1_funct_1(A_41,B_46)
      | ~ r2_hidden(C_47,k1_relat_1(A_41))
      | ~ r2_hidden(B_46,k1_relat_1(A_41))
      | ~ v2_funct_1(A_41)
      | ~ v1_funct_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_16093,plain,(
    ! [B_737,C_738] :
      ( B_737 = '#skF_7'('#skF_8','#skF_10')
      | k1_funct_1(k5_relat_1('#skF_10',C_738),B_737) != k1_funct_1(C_738,k1_funct_1('#skF_10','#skF_7'('#skF_8','#skF_10')))
      | ~ r2_hidden('#skF_7'('#skF_8','#skF_10'),k1_relat_1(k5_relat_1('#skF_10',C_738)))
      | ~ r2_hidden(B_737,k1_relat_1(k5_relat_1('#skF_10',C_738)))
      | ~ v2_funct_1(k5_relat_1('#skF_10',C_738))
      | ~ v1_funct_1(k5_relat_1('#skF_10',C_738))
      | ~ v1_relat_1(k5_relat_1('#skF_10',C_738))
      | ~ v1_funct_1(C_738)
      | ~ v1_relat_1(C_738) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13462,c_20])).

tff(c_16098,plain,(
    ! [B_737] :
      ( B_737 = '#skF_7'('#skF_8','#skF_10')
      | k1_funct_1(k5_relat_1('#skF_10','#skF_9'),B_737) != k1_funct_1('#skF_9',k1_funct_1('#skF_10','#skF_7'('#skF_8','#skF_10')))
      | ~ r2_hidden('#skF_7'('#skF_8','#skF_10'),k1_relat_1('#skF_9'))
      | ~ r2_hidden(B_737,k1_relat_1(k5_relat_1('#skF_10','#skF_9')))
      | ~ v2_funct_1(k5_relat_1('#skF_10','#skF_9'))
      | ~ v1_funct_1(k5_relat_1('#skF_10','#skF_9'))
      | ~ v1_relat_1(k5_relat_1('#skF_10','#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_16093])).

tff(c_16108,plain,(
    ! [B_739] :
      ( B_739 = '#skF_7'('#skF_8','#skF_10')
      | k1_funct_1('#skF_9',B_739) != k1_funct_1('#skF_9','#skF_7'('#skF_8','#skF_10'))
      | ~ r2_hidden(B_739,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_68,c_52,c_66,c_52,c_54,c_52,c_60,c_52,c_323,c_60,c_52,c_13379,c_16098])).

tff(c_16118,plain,
    ( k1_funct_1('#skF_10','#skF_7'('#skF_8','#skF_10')) = '#skF_7'('#skF_8','#skF_10')
    | ~ r2_hidden(k1_funct_1('#skF_10','#skF_7'('#skF_8','#skF_10')),'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_13379,c_16108])).

tff(c_16137,plain,(
    k1_funct_1('#skF_10','#skF_7'('#skF_8','#skF_10')) = '#skF_7'('#skF_8','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13526,c_16118])).

tff(c_16139,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10653,c_16137])).

%------------------------------------------------------------------------------
