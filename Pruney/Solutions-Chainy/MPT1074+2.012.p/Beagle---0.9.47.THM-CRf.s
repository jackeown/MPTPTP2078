%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:07 EST 2020

% Result     : Theorem 8.02s
% Output     : CNFRefutation 8.37s
% Verified   : 
% Statistics : Number of formulae       :  124 (1050 expanded)
%              Number of leaves         :   38 ( 382 expanded)
%              Depth                    :   26
%              Number of atoms          :  241 (3666 expanded)
%              Number of equality atoms :   37 ( 740 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_133,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ v1_xboole_0(B)
       => ! [C] :
            ( ~ v1_xboole_0(C)
           => ! [D] :
                ( ( v1_funct_1(D)
                  & v1_funct_2(D,B,C)
                  & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
               => ( ! [E] :
                      ( m1_subset_1(E,B)
                     => r2_hidden(k3_funct_2(B,C,D,E),A) )
                 => r1_tarski(k2_relset_1(B,C,D),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_funct_2)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_81,axiom,(
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

tff(f_111,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( k1_relat_1(C) = A
          & ! [D] :
              ( r2_hidden(D,A)
             => r2_hidden(k1_funct_1(C,D),B) ) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_56,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_156,plain,(
    ! [A_79,B_80,C_81] :
      ( k2_relset_1(A_79,B_80,C_81) = k2_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_170,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_156])).

tff(c_375,plain,(
    ! [A_115,B_116,C_117] :
      ( m1_subset_1(k2_relset_1(A_115,B_116,C_117),k1_zfmisc_1(B_116))
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_399,plain,
    ( m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1('#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_375])).

tff(c_405,plain,(
    m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_399])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ m1_subset_1(A_9,k1_zfmisc_1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_409,plain,(
    r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_405,c_12])).

tff(c_52,plain,(
    ~ r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_171,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_52])).

tff(c_109,plain,(
    ! [A_66,B_67] :
      ( r2_hidden('#skF_1'(A_66,B_67),A_66)
      | r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_120,plain,(
    ! [A_66] : r1_tarski(A_66,A_66) ),
    inference(resolution,[status(thm)],[c_109,c_4])).

tff(c_60,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_58,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_87,plain,(
    ! [C_58,A_59,B_60] :
      ( v1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_96,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_87])).

tff(c_346,plain,(
    ! [A_112,B_113,C_114] :
      ( k1_relset_1(A_112,B_113,C_114) = k1_relat_1(C_114)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_370,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_346])).

tff(c_2979,plain,(
    ! [B_311,A_312,C_313] :
      ( k1_xboole_0 = B_311
      | k1_relset_1(A_312,B_311,C_313) = A_312
      | ~ v1_funct_2(C_313,A_312,B_311)
      | ~ m1_subset_1(C_313,k1_zfmisc_1(k2_zfmisc_1(A_312,B_311))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3006,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_2979])).

tff(c_3016,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_370,c_3006])).

tff(c_3017,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3016])).

tff(c_3043,plain,(
    ! [C_316,B_317] :
      ( r2_hidden('#skF_2'(k1_relat_1(C_316),B_317,C_316),k1_relat_1(C_316))
      | v1_funct_2(C_316,k1_relat_1(C_316),B_317)
      | ~ v1_funct_1(C_316)
      | ~ v1_relat_1(C_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_3054,plain,(
    ! [B_317] :
      ( r2_hidden('#skF_2'('#skF_4',B_317,'#skF_6'),k1_relat_1('#skF_6'))
      | v1_funct_2('#skF_6',k1_relat_1('#skF_6'),B_317)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3017,c_3043])).

tff(c_3065,plain,(
    ! [B_318] :
      ( r2_hidden('#skF_2'('#skF_4',B_318,'#skF_6'),'#skF_4')
      | v1_funct_2('#skF_6','#skF_4',B_318) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_60,c_3017,c_3017,c_3054])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,B_8)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3076,plain,(
    ! [B_318] :
      ( m1_subset_1('#skF_2'('#skF_4',B_318,'#skF_6'),'#skF_4')
      | v1_funct_2('#skF_6','#skF_4',B_318) ) ),
    inference(resolution,[status(thm)],[c_3065,c_10])).

tff(c_6350,plain,(
    ! [A_573,B_574,C_575,D_576] :
      ( k3_funct_2(A_573,B_574,C_575,D_576) = k1_funct_1(C_575,D_576)
      | ~ m1_subset_1(D_576,A_573)
      | ~ m1_subset_1(C_575,k1_zfmisc_1(k2_zfmisc_1(A_573,B_574)))
      | ~ v1_funct_2(C_575,A_573,B_574)
      | ~ v1_funct_1(C_575)
      | v1_xboole_0(A_573) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_6354,plain,(
    ! [B_574,C_575,B_318] :
      ( k3_funct_2('#skF_4',B_574,C_575,'#skF_2'('#skF_4',B_318,'#skF_6')) = k1_funct_1(C_575,'#skF_2'('#skF_4',B_318,'#skF_6'))
      | ~ m1_subset_1(C_575,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_574)))
      | ~ v1_funct_2(C_575,'#skF_4',B_574)
      | ~ v1_funct_1(C_575)
      | v1_xboole_0('#skF_4')
      | v1_funct_2('#skF_6','#skF_4',B_318) ) ),
    inference(resolution,[status(thm)],[c_3076,c_6350])).

tff(c_6411,plain,(
    ! [B_580,C_581,B_582] :
      ( k3_funct_2('#skF_4',B_580,C_581,'#skF_2'('#skF_4',B_582,'#skF_6')) = k1_funct_1(C_581,'#skF_2'('#skF_4',B_582,'#skF_6'))
      | ~ m1_subset_1(C_581,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_580)))
      | ~ v1_funct_2(C_581,'#skF_4',B_580)
      | ~ v1_funct_1(C_581)
      | v1_funct_2('#skF_6','#skF_4',B_582) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_6354])).

tff(c_6433,plain,(
    ! [B_582] :
      ( k3_funct_2('#skF_4','#skF_5','#skF_6','#skF_2'('#skF_4',B_582,'#skF_6')) = k1_funct_1('#skF_6','#skF_2'('#skF_4',B_582,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6')
      | v1_funct_2('#skF_6','#skF_4',B_582) ) ),
    inference(resolution,[status(thm)],[c_56,c_6411])).

tff(c_8043,plain,(
    ! [B_659] :
      ( k3_funct_2('#skF_4','#skF_5','#skF_6','#skF_2'('#skF_4',B_659,'#skF_6')) = k1_funct_1('#skF_6','#skF_2'('#skF_4',B_659,'#skF_6'))
      | v1_funct_2('#skF_6','#skF_4',B_659) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_6433])).

tff(c_54,plain,(
    ! [E_47] :
      ( r2_hidden(k3_funct_2('#skF_4','#skF_5','#skF_6',E_47),'#skF_3')
      | ~ m1_subset_1(E_47,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_8313,plain,(
    ! [B_680] :
      ( r2_hidden(k1_funct_1('#skF_6','#skF_2'('#skF_4',B_680,'#skF_6')),'#skF_3')
      | ~ m1_subset_1('#skF_2'('#skF_4',B_680,'#skF_6'),'#skF_4')
      | v1_funct_2('#skF_6','#skF_4',B_680) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8043,c_54])).

tff(c_3192,plain,(
    ! [C_331,B_332] :
      ( ~ r2_hidden(k1_funct_1(C_331,'#skF_2'(k1_relat_1(C_331),B_332,C_331)),B_332)
      | v1_funct_2(C_331,k1_relat_1(C_331),B_332)
      | ~ v1_funct_1(C_331)
      | ~ v1_relat_1(C_331) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_3195,plain,(
    ! [B_332] :
      ( ~ r2_hidden(k1_funct_1('#skF_6','#skF_2'('#skF_4',B_332,'#skF_6')),B_332)
      | v1_funct_2('#skF_6',k1_relat_1('#skF_6'),B_332)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3017,c_3192])).

tff(c_3197,plain,(
    ! [B_332] :
      ( ~ r2_hidden(k1_funct_1('#skF_6','#skF_2'('#skF_4',B_332,'#skF_6')),B_332)
      | v1_funct_2('#skF_6','#skF_4',B_332) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_60,c_3017,c_3195])).

tff(c_8326,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_4','#skF_3','#skF_6'),'#skF_4')
    | v1_funct_2('#skF_6','#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_8313,c_3197])).

tff(c_8330,plain,(
    ~ m1_subset_1('#skF_2'('#skF_4','#skF_3','#skF_6'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_8326])).

tff(c_4781,plain,(
    ! [C_444,B_445] :
      ( r2_hidden('#skF_2'(k1_relat_1(C_444),B_445,C_444),k1_relat_1(C_444))
      | m1_subset_1(C_444,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_444),B_445)))
      | ~ v1_funct_1(C_444)
      | ~ v1_relat_1(C_444) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_4795,plain,(
    ! [B_445] :
      ( r2_hidden('#skF_2'(k1_relat_1('#skF_6'),B_445,'#skF_6'),'#skF_4')
      | m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),B_445)))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3017,c_4781])).

tff(c_6315,plain,(
    ! [B_572] :
      ( r2_hidden('#skF_2'('#skF_4',B_572,'#skF_6'),'#skF_4')
      | m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_572))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_60,c_3017,c_3017,c_4795])).

tff(c_24,plain,(
    ! [A_22,B_23,C_24] :
      ( k2_relset_1(A_22,B_23,C_24) = k2_relat_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6668,plain,(
    ! [B_594] :
      ( k2_relset_1('#skF_4',B_594,'#skF_6') = k2_relat_1('#skF_6')
      | r2_hidden('#skF_2'('#skF_4',B_594,'#skF_6'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6315,c_24])).

tff(c_6679,plain,(
    ! [B_594] :
      ( m1_subset_1('#skF_2'('#skF_4',B_594,'#skF_6'),'#skF_4')
      | k2_relset_1('#skF_4',B_594,'#skF_6') = k2_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_6668,c_10])).

tff(c_8340,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_6679,c_8330])).

tff(c_403,plain,(
    ! [A_115,B_116,C_117] :
      ( r1_tarski(k2_relset_1(A_115,B_116,C_117),B_116)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(resolution,[status(thm)],[c_375,c_12])).

tff(c_6680,plain,(
    ! [B_595] :
      ( r1_tarski(k2_relset_1('#skF_4',B_595,'#skF_6'),B_595)
      | r2_hidden('#skF_2'('#skF_4',B_595,'#skF_6'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6315,c_403])).

tff(c_6735,plain,(
    ! [B_595] :
      ( m1_subset_1('#skF_2'('#skF_4',B_595,'#skF_6'),'#skF_4')
      | r1_tarski(k2_relset_1('#skF_4',B_595,'#skF_6'),B_595) ) ),
    inference(resolution,[status(thm)],[c_6680,c_10])).

tff(c_8353,plain,
    ( m1_subset_1('#skF_2'('#skF_4','#skF_3','#skF_6'),'#skF_4')
    | r1_tarski(k2_relat_1('#skF_6'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8340,c_6735])).

tff(c_8365,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_171,c_8330,c_8353])).

tff(c_8367,plain,(
    m1_subset_1('#skF_2'('#skF_4','#skF_3','#skF_6'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_8326])).

tff(c_38,plain,(
    ! [A_28,B_29,C_30,D_31] :
      ( k3_funct_2(A_28,B_29,C_30,D_31) = k1_funct_1(C_30,D_31)
      | ~ m1_subset_1(D_31,A_28)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ v1_funct_2(C_30,A_28,B_29)
      | ~ v1_funct_1(C_30)
      | v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_8380,plain,(
    ! [B_29,C_30] :
      ( k3_funct_2('#skF_4',B_29,C_30,'#skF_2'('#skF_4','#skF_3','#skF_6')) = k1_funct_1(C_30,'#skF_2'('#skF_4','#skF_3','#skF_6'))
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_29)))
      | ~ v1_funct_2(C_30,'#skF_4',B_29)
      | ~ v1_funct_1(C_30)
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_8367,c_38])).

tff(c_8385,plain,(
    ! [B_683,C_684] :
      ( k3_funct_2('#skF_4',B_683,C_684,'#skF_2'('#skF_4','#skF_3','#skF_6')) = k1_funct_1(C_684,'#skF_2'('#skF_4','#skF_3','#skF_6'))
      | ~ m1_subset_1(C_684,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_683)))
      | ~ v1_funct_2(C_684,'#skF_4',B_683)
      | ~ v1_funct_1(C_684) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_8380])).

tff(c_8419,plain,
    ( k3_funct_2('#skF_4','#skF_5','#skF_6','#skF_2'('#skF_4','#skF_3','#skF_6')) = k1_funct_1('#skF_6','#skF_2'('#skF_4','#skF_3','#skF_6'))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_8385])).

tff(c_8432,plain,(
    k3_funct_2('#skF_4','#skF_5','#skF_6','#skF_2'('#skF_4','#skF_3','#skF_6')) = k1_funct_1('#skF_6','#skF_2'('#skF_4','#skF_3','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_8419])).

tff(c_149,plain,(
    ! [C_76,B_77,A_78] :
      ( r2_hidden(C_76,B_77)
      | ~ r2_hidden(C_76,A_78)
      | ~ r1_tarski(A_78,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_155,plain,(
    ! [E_47,B_77] :
      ( r2_hidden(k3_funct_2('#skF_4','#skF_5','#skF_6',E_47),B_77)
      | ~ r1_tarski('#skF_3',B_77)
      | ~ m1_subset_1(E_47,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_149])).

tff(c_8554,plain,(
    ! [B_77] :
      ( r2_hidden(k1_funct_1('#skF_6','#skF_2'('#skF_4','#skF_3','#skF_6')),B_77)
      | ~ r1_tarski('#skF_3',B_77)
      | ~ m1_subset_1('#skF_2'('#skF_4','#skF_3','#skF_6'),'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8432,c_155])).

tff(c_8580,plain,(
    ! [B_77] :
      ( r2_hidden(k1_funct_1('#skF_6','#skF_2'('#skF_4','#skF_3','#skF_6')),B_77)
      | ~ r1_tarski('#skF_3',B_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8367,c_8554])).

tff(c_6163,plain,(
    ! [C_552,B_553] :
      ( ~ r2_hidden(k1_funct_1(C_552,'#skF_2'(k1_relat_1(C_552),B_553,C_552)),B_553)
      | m1_subset_1(C_552,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_552),B_553)))
      | ~ v1_funct_1(C_552)
      | ~ v1_relat_1(C_552) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_6166,plain,(
    ! [B_553] :
      ( ~ r2_hidden(k1_funct_1('#skF_6','#skF_2'('#skF_4',B_553,'#skF_6')),B_553)
      | m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),B_553)))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3017,c_6163])).

tff(c_12057,plain,(
    ! [B_866] :
      ( ~ r2_hidden(k1_funct_1('#skF_6','#skF_2'('#skF_4',B_866,'#skF_6')),B_866)
      | m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_866))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_60,c_3017,c_6166])).

tff(c_12069,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_8580,c_12057])).

tff(c_12087,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_12069])).

tff(c_12160,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_12087,c_12])).

tff(c_12157,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_12087,c_24])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_3081,plain,(
    ! [A_323,B_324,C_325] :
      ( r1_tarski(k2_relset_1(A_323,B_324,C_325),B_324)
      | ~ m1_subset_1(C_325,k1_zfmisc_1(k2_zfmisc_1(A_323,B_324))) ) ),
    inference(resolution,[status(thm)],[c_375,c_12])).

tff(c_3108,plain,(
    ! [A_323,B_324,A_9] :
      ( r1_tarski(k2_relset_1(A_323,B_324,A_9),B_324)
      | ~ r1_tarski(A_9,k2_zfmisc_1(A_323,B_324)) ) ),
    inference(resolution,[status(thm)],[c_14,c_3081])).

tff(c_12311,plain,
    ( r1_tarski(k2_relat_1('#skF_6'),'#skF_3')
    | ~ r1_tarski('#skF_6',k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12157,c_3108])).

tff(c_12321,plain,(
    r1_tarski(k2_relat_1('#skF_6'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12160,c_12311])).

tff(c_12323,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_171,c_12321])).

tff(c_12324,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3016])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_12350,plain,(
    ! [A_869] : r1_tarski('#skF_5',A_869) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12324,c_8])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_232,plain,(
    ! [A_94,B_95,B_96] :
      ( r2_hidden('#skF_1'(A_94,B_95),B_96)
      | ~ r1_tarski(A_94,B_96)
      | r1_tarski(A_94,B_95) ) ),
    inference(resolution,[status(thm)],[c_6,c_149])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( ~ r1_tarski(B_12,A_11)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_247,plain,(
    ! [B_96,A_94,B_95] :
      ( ~ r1_tarski(B_96,'#skF_1'(A_94,B_95))
      | ~ r1_tarski(A_94,B_96)
      | r1_tarski(A_94,B_95) ) ),
    inference(resolution,[status(thm)],[c_232,c_16])).

tff(c_12456,plain,(
    ! [A_881,B_882] :
      ( ~ r1_tarski(A_881,'#skF_5')
      | r1_tarski(A_881,B_882) ) ),
    inference(resolution,[status(thm)],[c_12350,c_247])).

tff(c_12474,plain,(
    ! [B_882] : r1_tarski(k2_relat_1('#skF_6'),B_882) ),
    inference(resolution,[status(thm)],[c_409,c_12456])).

tff(c_12481,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12474,c_171])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:33:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.02/3.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.02/3.08  
% 8.02/3.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.02/3.08  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 8.02/3.08  
% 8.02/3.08  %Foreground sorts:
% 8.02/3.08  
% 8.02/3.08  
% 8.02/3.08  %Background operators:
% 8.02/3.08  
% 8.02/3.08  
% 8.02/3.08  %Foreground operators:
% 8.02/3.08  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.02/3.08  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.02/3.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.02/3.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.02/3.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.02/3.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.02/3.08  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.02/3.08  tff('#skF_5', type, '#skF_5': $i).
% 8.02/3.08  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.02/3.08  tff('#skF_6', type, '#skF_6': $i).
% 8.02/3.08  tff('#skF_3', type, '#skF_3': $i).
% 8.02/3.08  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.02/3.08  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.02/3.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.02/3.08  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.02/3.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.02/3.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.02/3.08  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.02/3.08  tff('#skF_4', type, '#skF_4': $i).
% 8.02/3.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.02/3.08  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.02/3.08  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.02/3.08  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 8.02/3.08  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.02/3.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.02/3.08  
% 8.37/3.10  tff(f_133, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((![E]: (m1_subset_1(E, B) => r2_hidden(k3_funct_2(B, C, D, E), A))) => r1_tarski(k2_relset_1(B, C, D), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t191_funct_2)).
% 8.37/3.10  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.37/3.10  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 8.37/3.10  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.37/3.10  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 8.37/3.10  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.37/3.10  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.37/3.10  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 8.37/3.10  tff(f_111, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_funct_2)).
% 8.37/3.10  tff(f_38, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 8.37/3.10  tff(f_94, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 8.37/3.10  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.37/3.10  tff(f_47, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 8.37/3.10  tff(c_56, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 8.37/3.10  tff(c_156, plain, (![A_79, B_80, C_81]: (k2_relset_1(A_79, B_80, C_81)=k2_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.37/3.10  tff(c_170, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_156])).
% 8.37/3.10  tff(c_375, plain, (![A_115, B_116, C_117]: (m1_subset_1(k2_relset_1(A_115, B_116, C_117), k1_zfmisc_1(B_116)) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.37/3.10  tff(c_399, plain, (m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_170, c_375])).
% 8.37/3.10  tff(c_405, plain, (m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_399])).
% 8.37/3.10  tff(c_12, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~m1_subset_1(A_9, k1_zfmisc_1(B_10)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.37/3.10  tff(c_409, plain, (r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_405, c_12])).
% 8.37/3.10  tff(c_52, plain, (~r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_133])).
% 8.37/3.10  tff(c_171, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_170, c_52])).
% 8.37/3.10  tff(c_109, plain, (![A_66, B_67]: (r2_hidden('#skF_1'(A_66, B_67), A_66) | r1_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.37/3.10  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.37/3.10  tff(c_120, plain, (![A_66]: (r1_tarski(A_66, A_66))), inference(resolution, [status(thm)], [c_109, c_4])).
% 8.37/3.10  tff(c_60, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_133])).
% 8.37/3.10  tff(c_58, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_133])).
% 8.37/3.10  tff(c_64, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 8.37/3.10  tff(c_87, plain, (![C_58, A_59, B_60]: (v1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.37/3.10  tff(c_96, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_87])).
% 8.37/3.10  tff(c_346, plain, (![A_112, B_113, C_114]: (k1_relset_1(A_112, B_113, C_114)=k1_relat_1(C_114) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.37/3.10  tff(c_370, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_346])).
% 8.37/3.10  tff(c_2979, plain, (![B_311, A_312, C_313]: (k1_xboole_0=B_311 | k1_relset_1(A_312, B_311, C_313)=A_312 | ~v1_funct_2(C_313, A_312, B_311) | ~m1_subset_1(C_313, k1_zfmisc_1(k2_zfmisc_1(A_312, B_311))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.37/3.10  tff(c_3006, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_56, c_2979])).
% 8.37/3.10  tff(c_3016, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_370, c_3006])).
% 8.37/3.10  tff(c_3017, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_3016])).
% 8.37/3.10  tff(c_3043, plain, (![C_316, B_317]: (r2_hidden('#skF_2'(k1_relat_1(C_316), B_317, C_316), k1_relat_1(C_316)) | v1_funct_2(C_316, k1_relat_1(C_316), B_317) | ~v1_funct_1(C_316) | ~v1_relat_1(C_316))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.37/3.10  tff(c_3054, plain, (![B_317]: (r2_hidden('#skF_2'('#skF_4', B_317, '#skF_6'), k1_relat_1('#skF_6')) | v1_funct_2('#skF_6', k1_relat_1('#skF_6'), B_317) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3017, c_3043])).
% 8.37/3.10  tff(c_3065, plain, (![B_318]: (r2_hidden('#skF_2'('#skF_4', B_318, '#skF_6'), '#skF_4') | v1_funct_2('#skF_6', '#skF_4', B_318))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_60, c_3017, c_3017, c_3054])).
% 8.37/3.10  tff(c_10, plain, (![A_7, B_8]: (m1_subset_1(A_7, B_8) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.37/3.10  tff(c_3076, plain, (![B_318]: (m1_subset_1('#skF_2'('#skF_4', B_318, '#skF_6'), '#skF_4') | v1_funct_2('#skF_6', '#skF_4', B_318))), inference(resolution, [status(thm)], [c_3065, c_10])).
% 8.37/3.10  tff(c_6350, plain, (![A_573, B_574, C_575, D_576]: (k3_funct_2(A_573, B_574, C_575, D_576)=k1_funct_1(C_575, D_576) | ~m1_subset_1(D_576, A_573) | ~m1_subset_1(C_575, k1_zfmisc_1(k2_zfmisc_1(A_573, B_574))) | ~v1_funct_2(C_575, A_573, B_574) | ~v1_funct_1(C_575) | v1_xboole_0(A_573))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.37/3.10  tff(c_6354, plain, (![B_574, C_575, B_318]: (k3_funct_2('#skF_4', B_574, C_575, '#skF_2'('#skF_4', B_318, '#skF_6'))=k1_funct_1(C_575, '#skF_2'('#skF_4', B_318, '#skF_6')) | ~m1_subset_1(C_575, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_574))) | ~v1_funct_2(C_575, '#skF_4', B_574) | ~v1_funct_1(C_575) | v1_xboole_0('#skF_4') | v1_funct_2('#skF_6', '#skF_4', B_318))), inference(resolution, [status(thm)], [c_3076, c_6350])).
% 8.37/3.10  tff(c_6411, plain, (![B_580, C_581, B_582]: (k3_funct_2('#skF_4', B_580, C_581, '#skF_2'('#skF_4', B_582, '#skF_6'))=k1_funct_1(C_581, '#skF_2'('#skF_4', B_582, '#skF_6')) | ~m1_subset_1(C_581, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_580))) | ~v1_funct_2(C_581, '#skF_4', B_580) | ~v1_funct_1(C_581) | v1_funct_2('#skF_6', '#skF_4', B_582))), inference(negUnitSimplification, [status(thm)], [c_64, c_6354])).
% 8.37/3.10  tff(c_6433, plain, (![B_582]: (k3_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_2'('#skF_4', B_582, '#skF_6'))=k1_funct_1('#skF_6', '#skF_2'('#skF_4', B_582, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | v1_funct_2('#skF_6', '#skF_4', B_582))), inference(resolution, [status(thm)], [c_56, c_6411])).
% 8.37/3.10  tff(c_8043, plain, (![B_659]: (k3_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_2'('#skF_4', B_659, '#skF_6'))=k1_funct_1('#skF_6', '#skF_2'('#skF_4', B_659, '#skF_6')) | v1_funct_2('#skF_6', '#skF_4', B_659))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_6433])).
% 8.37/3.10  tff(c_54, plain, (![E_47]: (r2_hidden(k3_funct_2('#skF_4', '#skF_5', '#skF_6', E_47), '#skF_3') | ~m1_subset_1(E_47, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 8.37/3.10  tff(c_8313, plain, (![B_680]: (r2_hidden(k1_funct_1('#skF_6', '#skF_2'('#skF_4', B_680, '#skF_6')), '#skF_3') | ~m1_subset_1('#skF_2'('#skF_4', B_680, '#skF_6'), '#skF_4') | v1_funct_2('#skF_6', '#skF_4', B_680))), inference(superposition, [status(thm), theory('equality')], [c_8043, c_54])).
% 8.37/3.10  tff(c_3192, plain, (![C_331, B_332]: (~r2_hidden(k1_funct_1(C_331, '#skF_2'(k1_relat_1(C_331), B_332, C_331)), B_332) | v1_funct_2(C_331, k1_relat_1(C_331), B_332) | ~v1_funct_1(C_331) | ~v1_relat_1(C_331))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.37/3.10  tff(c_3195, plain, (![B_332]: (~r2_hidden(k1_funct_1('#skF_6', '#skF_2'('#skF_4', B_332, '#skF_6')), B_332) | v1_funct_2('#skF_6', k1_relat_1('#skF_6'), B_332) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3017, c_3192])).
% 8.37/3.10  tff(c_3197, plain, (![B_332]: (~r2_hidden(k1_funct_1('#skF_6', '#skF_2'('#skF_4', B_332, '#skF_6')), B_332) | v1_funct_2('#skF_6', '#skF_4', B_332))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_60, c_3017, c_3195])).
% 8.37/3.10  tff(c_8326, plain, (~m1_subset_1('#skF_2'('#skF_4', '#skF_3', '#skF_6'), '#skF_4') | v1_funct_2('#skF_6', '#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_8313, c_3197])).
% 8.37/3.10  tff(c_8330, plain, (~m1_subset_1('#skF_2'('#skF_4', '#skF_3', '#skF_6'), '#skF_4')), inference(splitLeft, [status(thm)], [c_8326])).
% 8.37/3.10  tff(c_4781, plain, (![C_444, B_445]: (r2_hidden('#skF_2'(k1_relat_1(C_444), B_445, C_444), k1_relat_1(C_444)) | m1_subset_1(C_444, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_444), B_445))) | ~v1_funct_1(C_444) | ~v1_relat_1(C_444))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.37/3.10  tff(c_4795, plain, (![B_445]: (r2_hidden('#skF_2'(k1_relat_1('#skF_6'), B_445, '#skF_6'), '#skF_4') | m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), B_445))) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3017, c_4781])).
% 8.37/3.10  tff(c_6315, plain, (![B_572]: (r2_hidden('#skF_2'('#skF_4', B_572, '#skF_6'), '#skF_4') | m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_572))))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_60, c_3017, c_3017, c_4795])).
% 8.37/3.10  tff(c_24, plain, (![A_22, B_23, C_24]: (k2_relset_1(A_22, B_23, C_24)=k2_relat_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.37/3.10  tff(c_6668, plain, (![B_594]: (k2_relset_1('#skF_4', B_594, '#skF_6')=k2_relat_1('#skF_6') | r2_hidden('#skF_2'('#skF_4', B_594, '#skF_6'), '#skF_4'))), inference(resolution, [status(thm)], [c_6315, c_24])).
% 8.37/3.10  tff(c_6679, plain, (![B_594]: (m1_subset_1('#skF_2'('#skF_4', B_594, '#skF_6'), '#skF_4') | k2_relset_1('#skF_4', B_594, '#skF_6')=k2_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_6668, c_10])).
% 8.37/3.10  tff(c_8340, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_6679, c_8330])).
% 8.37/3.10  tff(c_403, plain, (![A_115, B_116, C_117]: (r1_tarski(k2_relset_1(A_115, B_116, C_117), B_116) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(resolution, [status(thm)], [c_375, c_12])).
% 8.37/3.10  tff(c_6680, plain, (![B_595]: (r1_tarski(k2_relset_1('#skF_4', B_595, '#skF_6'), B_595) | r2_hidden('#skF_2'('#skF_4', B_595, '#skF_6'), '#skF_4'))), inference(resolution, [status(thm)], [c_6315, c_403])).
% 8.37/3.10  tff(c_6735, plain, (![B_595]: (m1_subset_1('#skF_2'('#skF_4', B_595, '#skF_6'), '#skF_4') | r1_tarski(k2_relset_1('#skF_4', B_595, '#skF_6'), B_595))), inference(resolution, [status(thm)], [c_6680, c_10])).
% 8.37/3.10  tff(c_8353, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_3', '#skF_6'), '#skF_4') | r1_tarski(k2_relat_1('#skF_6'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8340, c_6735])).
% 8.37/3.10  tff(c_8365, plain, $false, inference(negUnitSimplification, [status(thm)], [c_171, c_8330, c_8353])).
% 8.37/3.10  tff(c_8367, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_3', '#skF_6'), '#skF_4')), inference(splitRight, [status(thm)], [c_8326])).
% 8.37/3.10  tff(c_38, plain, (![A_28, B_29, C_30, D_31]: (k3_funct_2(A_28, B_29, C_30, D_31)=k1_funct_1(C_30, D_31) | ~m1_subset_1(D_31, A_28) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~v1_funct_2(C_30, A_28, B_29) | ~v1_funct_1(C_30) | v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.37/3.10  tff(c_8380, plain, (![B_29, C_30]: (k3_funct_2('#skF_4', B_29, C_30, '#skF_2'('#skF_4', '#skF_3', '#skF_6'))=k1_funct_1(C_30, '#skF_2'('#skF_4', '#skF_3', '#skF_6')) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_29))) | ~v1_funct_2(C_30, '#skF_4', B_29) | ~v1_funct_1(C_30) | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_8367, c_38])).
% 8.37/3.10  tff(c_8385, plain, (![B_683, C_684]: (k3_funct_2('#skF_4', B_683, C_684, '#skF_2'('#skF_4', '#skF_3', '#skF_6'))=k1_funct_1(C_684, '#skF_2'('#skF_4', '#skF_3', '#skF_6')) | ~m1_subset_1(C_684, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_683))) | ~v1_funct_2(C_684, '#skF_4', B_683) | ~v1_funct_1(C_684))), inference(negUnitSimplification, [status(thm)], [c_64, c_8380])).
% 8.37/3.10  tff(c_8419, plain, (k3_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_2'('#skF_4', '#skF_3', '#skF_6'))=k1_funct_1('#skF_6', '#skF_2'('#skF_4', '#skF_3', '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_8385])).
% 8.37/3.10  tff(c_8432, plain, (k3_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_2'('#skF_4', '#skF_3', '#skF_6'))=k1_funct_1('#skF_6', '#skF_2'('#skF_4', '#skF_3', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_8419])).
% 8.37/3.10  tff(c_149, plain, (![C_76, B_77, A_78]: (r2_hidden(C_76, B_77) | ~r2_hidden(C_76, A_78) | ~r1_tarski(A_78, B_77))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.37/3.10  tff(c_155, plain, (![E_47, B_77]: (r2_hidden(k3_funct_2('#skF_4', '#skF_5', '#skF_6', E_47), B_77) | ~r1_tarski('#skF_3', B_77) | ~m1_subset_1(E_47, '#skF_4'))), inference(resolution, [status(thm)], [c_54, c_149])).
% 8.37/3.10  tff(c_8554, plain, (![B_77]: (r2_hidden(k1_funct_1('#skF_6', '#skF_2'('#skF_4', '#skF_3', '#skF_6')), B_77) | ~r1_tarski('#skF_3', B_77) | ~m1_subset_1('#skF_2'('#skF_4', '#skF_3', '#skF_6'), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8432, c_155])).
% 8.37/3.10  tff(c_8580, plain, (![B_77]: (r2_hidden(k1_funct_1('#skF_6', '#skF_2'('#skF_4', '#skF_3', '#skF_6')), B_77) | ~r1_tarski('#skF_3', B_77))), inference(demodulation, [status(thm), theory('equality')], [c_8367, c_8554])).
% 8.37/3.10  tff(c_6163, plain, (![C_552, B_553]: (~r2_hidden(k1_funct_1(C_552, '#skF_2'(k1_relat_1(C_552), B_553, C_552)), B_553) | m1_subset_1(C_552, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_552), B_553))) | ~v1_funct_1(C_552) | ~v1_relat_1(C_552))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.37/3.10  tff(c_6166, plain, (![B_553]: (~r2_hidden(k1_funct_1('#skF_6', '#skF_2'('#skF_4', B_553, '#skF_6')), B_553) | m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), B_553))) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3017, c_6163])).
% 8.37/3.10  tff(c_12057, plain, (![B_866]: (~r2_hidden(k1_funct_1('#skF_6', '#skF_2'('#skF_4', B_866, '#skF_6')), B_866) | m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_866))))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_60, c_3017, c_6166])).
% 8.37/3.10  tff(c_12069, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_8580, c_12057])).
% 8.37/3.10  tff(c_12087, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_12069])).
% 8.37/3.10  tff(c_12160, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_12087, c_12])).
% 8.37/3.10  tff(c_12157, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_12087, c_24])).
% 8.37/3.10  tff(c_14, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.37/3.10  tff(c_3081, plain, (![A_323, B_324, C_325]: (r1_tarski(k2_relset_1(A_323, B_324, C_325), B_324) | ~m1_subset_1(C_325, k1_zfmisc_1(k2_zfmisc_1(A_323, B_324))))), inference(resolution, [status(thm)], [c_375, c_12])).
% 8.37/3.10  tff(c_3108, plain, (![A_323, B_324, A_9]: (r1_tarski(k2_relset_1(A_323, B_324, A_9), B_324) | ~r1_tarski(A_9, k2_zfmisc_1(A_323, B_324)))), inference(resolution, [status(thm)], [c_14, c_3081])).
% 8.37/3.10  tff(c_12311, plain, (r1_tarski(k2_relat_1('#skF_6'), '#skF_3') | ~r1_tarski('#skF_6', k2_zfmisc_1('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_12157, c_3108])).
% 8.37/3.10  tff(c_12321, plain, (r1_tarski(k2_relat_1('#skF_6'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12160, c_12311])).
% 8.37/3.10  tff(c_12323, plain, $false, inference(negUnitSimplification, [status(thm)], [c_171, c_12321])).
% 8.37/3.10  tff(c_12324, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_3016])).
% 8.37/3.10  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.37/3.10  tff(c_12350, plain, (![A_869]: (r1_tarski('#skF_5', A_869))), inference(demodulation, [status(thm), theory('equality')], [c_12324, c_8])).
% 8.37/3.10  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.37/3.10  tff(c_232, plain, (![A_94, B_95, B_96]: (r2_hidden('#skF_1'(A_94, B_95), B_96) | ~r1_tarski(A_94, B_96) | r1_tarski(A_94, B_95))), inference(resolution, [status(thm)], [c_6, c_149])).
% 8.37/3.10  tff(c_16, plain, (![B_12, A_11]: (~r1_tarski(B_12, A_11) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.37/3.10  tff(c_247, plain, (![B_96, A_94, B_95]: (~r1_tarski(B_96, '#skF_1'(A_94, B_95)) | ~r1_tarski(A_94, B_96) | r1_tarski(A_94, B_95))), inference(resolution, [status(thm)], [c_232, c_16])).
% 8.37/3.10  tff(c_12456, plain, (![A_881, B_882]: (~r1_tarski(A_881, '#skF_5') | r1_tarski(A_881, B_882))), inference(resolution, [status(thm)], [c_12350, c_247])).
% 8.37/3.10  tff(c_12474, plain, (![B_882]: (r1_tarski(k2_relat_1('#skF_6'), B_882))), inference(resolution, [status(thm)], [c_409, c_12456])).
% 8.37/3.10  tff(c_12481, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12474, c_171])).
% 8.37/3.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.37/3.10  
% 8.37/3.10  Inference rules
% 8.37/3.10  ----------------------
% 8.37/3.10  #Ref     : 0
% 8.37/3.10  #Sup     : 2484
% 8.37/3.10  #Fact    : 0
% 8.37/3.10  #Define  : 0
% 8.37/3.10  #Split   : 35
% 8.37/3.10  #Chain   : 0
% 8.37/3.10  #Close   : 0
% 8.37/3.10  
% 8.37/3.10  Ordering : KBO
% 8.37/3.10  
% 8.37/3.10  Simplification rules
% 8.37/3.10  ----------------------
% 8.37/3.10  #Subsume      : 505
% 8.37/3.10  #Demod        : 1562
% 8.37/3.10  #Tautology    : 778
% 8.37/3.10  #SimpNegUnit  : 46
% 8.37/3.10  #BackRed      : 210
% 8.37/3.10  
% 8.37/3.10  #Partial instantiations: 0
% 8.37/3.10  #Strategies tried      : 1
% 8.37/3.10  
% 8.37/3.10  Timing (in seconds)
% 8.37/3.10  ----------------------
% 8.37/3.10  Preprocessing        : 0.34
% 8.37/3.10  Parsing              : 0.17
% 8.37/3.10  CNF conversion       : 0.02
% 8.37/3.10  Main loop            : 1.97
% 8.37/3.10  Inferencing          : 0.62
% 8.37/3.10  Reduction            : 0.71
% 8.37/3.10  Demodulation         : 0.48
% 8.37/3.10  BG Simplification    : 0.07
% 8.37/3.10  Subsumption          : 0.39
% 8.37/3.10  Abstraction          : 0.09
% 8.37/3.10  MUC search           : 0.00
% 8.37/3.10  Cooper               : 0.00
% 8.37/3.10  Total                : 2.35
% 8.37/3.10  Index Insertion      : 0.00
% 8.37/3.10  Index Deletion       : 0.00
% 8.37/3.10  Index Matching       : 0.00
% 8.37/3.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
