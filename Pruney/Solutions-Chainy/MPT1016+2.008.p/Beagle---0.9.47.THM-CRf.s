%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:41 EST 2020

% Result     : Theorem 4.79s
% Output     : CNFRefutation 4.79s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 462 expanded)
%              Number of leaves         :   33 ( 167 expanded)
%              Depth                    :   15
%              Number of atoms          :  300 (1631 expanded)
%              Number of equality atoms :   78 ( 413 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_112,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( v2_funct_1(B)
        <=> ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A)
                & k1_funct_1(B,C) = k1_funct_1(B,D) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_65,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(D)
          & r2_hidden(C,A) )
       => ( B = k1_xboole_0
          | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_34,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_40,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_38,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_79,plain,(
    ! [C_46,A_47,B_48] :
      ( v1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_92,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_79])).

tff(c_141,plain,(
    ! [C_63,A_64,B_65] :
      ( v4_relat_1(C_63,A_64)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_154,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_141])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k1_relat_1(B_12),A_11)
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_42,plain,
    ( '#skF_5' != '#skF_6'
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_61,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_208,plain,(
    ! [A_81] :
      ( r2_hidden('#skF_1'(A_81),k1_relat_1(A_81))
      | v2_funct_1(A_81)
      | ~ v1_funct_1(A_81)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1074,plain,(
    ! [A_172,A_173] :
      ( r2_hidden('#skF_1'(A_172),A_173)
      | ~ m1_subset_1(k1_relat_1(A_172),k1_zfmisc_1(A_173))
      | v2_funct_1(A_172)
      | ~ v1_funct_1(A_172)
      | ~ v1_relat_1(A_172) ) ),
    inference(resolution,[status(thm)],[c_208,c_2])).

tff(c_1276,plain,(
    ! [A_191,B_192] :
      ( r2_hidden('#skF_1'(A_191),B_192)
      | v2_funct_1(A_191)
      | ~ v1_funct_1(A_191)
      | ~ v1_relat_1(A_191)
      | ~ r1_tarski(k1_relat_1(A_191),B_192) ) ),
    inference(resolution,[status(thm)],[c_8,c_1074])).

tff(c_189,plain,(
    ! [A_72] :
      ( '#skF_2'(A_72) != '#skF_1'(A_72)
      | v2_funct_1(A_72)
      | ~ v1_funct_1(A_72)
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_192,plain,
    ( '#skF_2'('#skF_4') != '#skF_1'('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_189,c_61])).

tff(c_195,plain,(
    '#skF_2'('#skF_4') != '#skF_1'('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_40,c_192])).

tff(c_229,plain,(
    ! [A_89] :
      ( r2_hidden('#skF_2'(A_89),k1_relat_1(A_89))
      | v2_funct_1(A_89)
      | ~ v1_funct_1(A_89)
      | ~ v1_relat_1(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_539,plain,(
    ! [A_122,A_123] :
      ( r2_hidden('#skF_2'(A_122),A_123)
      | ~ m1_subset_1(k1_relat_1(A_122),k1_zfmisc_1(A_123))
      | v2_funct_1(A_122)
      | ~ v1_funct_1(A_122)
      | ~ v1_relat_1(A_122) ) ),
    inference(resolution,[status(thm)],[c_229,c_2])).

tff(c_782,plain,(
    ! [A_145,B_146] :
      ( r2_hidden('#skF_2'(A_145),B_146)
      | v2_funct_1(A_145)
      | ~ v1_funct_1(A_145)
      | ~ v1_relat_1(A_145)
      | ~ r1_tarski(k1_relat_1(A_145),B_146) ) ),
    inference(resolution,[status(thm)],[c_8,c_539])).

tff(c_255,plain,(
    ! [A_92] :
      ( k1_funct_1(A_92,'#skF_2'(A_92)) = k1_funct_1(A_92,'#skF_1'(A_92))
      | v2_funct_1(A_92)
      | ~ v1_funct_1(A_92)
      | ~ v1_relat_1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_60,plain,(
    ! [D_37,C_36] :
      ( v2_funct_1('#skF_4')
      | D_37 = C_36
      | k1_funct_1('#skF_4',D_37) != k1_funct_1('#skF_4',C_36)
      | ~ r2_hidden(D_37,'#skF_3')
      | ~ r2_hidden(C_36,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_109,plain,(
    ! [D_37,C_36] :
      ( D_37 = C_36
      | k1_funct_1('#skF_4',D_37) != k1_funct_1('#skF_4',C_36)
      | ~ r2_hidden(D_37,'#skF_3')
      | ~ r2_hidden(C_36,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_60])).

tff(c_261,plain,(
    ! [C_36] :
      ( C_36 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_36) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_36,'#skF_3')
      | v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_109])).

tff(c_270,plain,(
    ! [C_36] :
      ( C_36 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_36) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_36,'#skF_3')
      | v2_funct_1('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_40,c_261])).

tff(c_271,plain,(
    ! [C_36] :
      ( C_36 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_36) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_36,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_270])).

tff(c_374,plain,(
    ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_271])).

tff(c_787,plain,
    ( v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_782,c_374])).

tff(c_801,plain,
    ( v2_funct_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_40,c_787])).

tff(c_802,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_801])).

tff(c_809,plain,
    ( ~ v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_802])).

tff(c_813,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_154,c_809])).

tff(c_815,plain,(
    r2_hidden('#skF_2'('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_271])).

tff(c_264,plain,(
    ! [D_37] :
      ( D_37 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_37) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_37,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_109])).

tff(c_273,plain,(
    ! [D_37] :
      ( D_37 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_37) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_37,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | v2_funct_1('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_40,c_264])).

tff(c_274,plain,(
    ! [D_37] :
      ( D_37 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_37) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_37,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_273])).

tff(c_872,plain,(
    ! [D_37] :
      ( D_37 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_37) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_37,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_815,c_274])).

tff(c_875,plain,
    ( '#skF_2'('#skF_4') = '#skF_1'('#skF_4')
    | ~ r2_hidden('#skF_1'('#skF_4'),'#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_872])).

tff(c_876,plain,(
    ~ r2_hidden('#skF_1'('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_195,c_875])).

tff(c_1284,plain,
    ( v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1276,c_876])).

tff(c_1299,plain,
    ( v2_funct_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_40,c_1284])).

tff(c_1300,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_1299])).

tff(c_1307,plain,
    ( ~ v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_1300])).

tff(c_1311,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_154,c_1307])).

tff(c_1313,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_46,plain,
    ( r2_hidden('#skF_6','#skF_3')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1316,plain,(
    r2_hidden('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1313,c_46])).

tff(c_1990,plain,(
    ! [D_294,C_295,B_296,A_297] :
      ( k1_funct_1(k2_funct_1(D_294),k1_funct_1(D_294,C_295)) = C_295
      | k1_xboole_0 = B_296
      | ~ r2_hidden(C_295,A_297)
      | ~ v2_funct_1(D_294)
      | ~ m1_subset_1(D_294,k1_zfmisc_1(k2_zfmisc_1(A_297,B_296)))
      | ~ v1_funct_2(D_294,A_297,B_296)
      | ~ v1_funct_1(D_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2025,plain,(
    ! [D_300,B_301] :
      ( k1_funct_1(k2_funct_1(D_300),k1_funct_1(D_300,'#skF_6')) = '#skF_6'
      | k1_xboole_0 = B_301
      | ~ v2_funct_1(D_300)
      | ~ m1_subset_1(D_300,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_301)))
      | ~ v1_funct_2(D_300,'#skF_3',B_301)
      | ~ v1_funct_1(D_300) ) ),
    inference(resolution,[status(thm)],[c_1316,c_1990])).

tff(c_2030,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_2025])).

tff(c_2037,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1313,c_2030])).

tff(c_2125,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2037])).

tff(c_4,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1329,plain,(
    ! [A_198,B_199] :
      ( r1_tarski(A_198,B_199)
      | ~ m1_subset_1(A_198,k1_zfmisc_1(B_199)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1341,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(resolution,[status(thm)],[c_4,c_1329])).

tff(c_2145,plain,(
    ! [A_5] : r1_tarski('#skF_3',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2125,c_1341])).

tff(c_1312,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1435,plain,(
    ! [C_221,A_222,B_223] :
      ( r2_hidden(C_221,A_222)
      | ~ r2_hidden(C_221,B_223)
      | ~ m1_subset_1(B_223,k1_zfmisc_1(A_222)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1467,plain,(
    ! [A_228] :
      ( r2_hidden('#skF_6',A_228)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_228)) ) ),
    inference(resolution,[status(thm)],[c_1316,c_1435])).

tff(c_1472,plain,(
    ! [B_7] :
      ( r2_hidden('#skF_6',B_7)
      | ~ r1_tarski('#skF_3',B_7) ) ),
    inference(resolution,[status(thm)],[c_8,c_1467])).

tff(c_44,plain,
    ( k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1343,plain,(
    k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1313,c_44])).

tff(c_48,plain,
    ( r2_hidden('#skF_5','#skF_3')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1318,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1313,c_48])).

tff(c_1809,plain,(
    ! [D_282,C_283,B_284,A_285] :
      ( k1_funct_1(k2_funct_1(D_282),k1_funct_1(D_282,C_283)) = C_283
      | k1_xboole_0 = B_284
      | ~ r2_hidden(C_283,A_285)
      | ~ v2_funct_1(D_282)
      | ~ m1_subset_1(D_282,k1_zfmisc_1(k2_zfmisc_1(A_285,B_284)))
      | ~ v1_funct_2(D_282,A_285,B_284)
      | ~ v1_funct_1(D_282) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1856,plain,(
    ! [D_287,B_288] :
      ( k1_funct_1(k2_funct_1(D_287),k1_funct_1(D_287,'#skF_5')) = '#skF_5'
      | k1_xboole_0 = B_288
      | ~ v2_funct_1(D_287)
      | ~ m1_subset_1(D_287,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_288)))
      | ~ v1_funct_2(D_287,'#skF_3',B_288)
      | ~ v1_funct_1(D_287) ) ),
    inference(resolution,[status(thm)],[c_1318,c_1809])).

tff(c_1861,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_1856])).

tff(c_1868,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_5'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1313,c_1343,c_1861])).

tff(c_1870,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1868])).

tff(c_1892,plain,(
    ! [A_5] : r1_tarski('#skF_3',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1870,c_1341])).

tff(c_1443,plain,(
    ! [A_225] :
      ( r2_hidden('#skF_5',A_225)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_225)) ) ),
    inference(resolution,[status(thm)],[c_1318,c_1435])).

tff(c_1448,plain,(
    ! [B_7] :
      ( r2_hidden('#skF_5',B_7)
      | ~ r1_tarski('#skF_3',B_7) ) ),
    inference(resolution,[status(thm)],[c_8,c_1443])).

tff(c_1349,plain,(
    ! [C_201,A_202,B_203] :
      ( v1_relat_1(C_201)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(A_202,B_203))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1362,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_1349])).

tff(c_1734,plain,(
    ! [C_277,B_278,A_279] :
      ( C_277 = B_278
      | k1_funct_1(A_279,C_277) != k1_funct_1(A_279,B_278)
      | ~ r2_hidden(C_277,k1_relat_1(A_279))
      | ~ r2_hidden(B_278,k1_relat_1(A_279))
      | ~ v2_funct_1(A_279)
      | ~ v1_funct_1(A_279)
      | ~ v1_relat_1(A_279) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1742,plain,(
    ! [C_277] :
      ( C_277 = '#skF_5'
      | k1_funct_1('#skF_4',C_277) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden(C_277,k1_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_5',k1_relat_1('#skF_4'))
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1343,c_1734])).

tff(c_1746,plain,(
    ! [C_277] :
      ( C_277 = '#skF_5'
      | k1_funct_1('#skF_4',C_277) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden(C_277,k1_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_5',k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1362,c_40,c_1313,c_1742])).

tff(c_1775,plain,(
    ~ r2_hidden('#skF_5',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1746])).

tff(c_1779,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1448,c_1775])).

tff(c_1943,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1892,c_1779])).

tff(c_1945,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1868])).

tff(c_1946,plain,(
    ! [D_292,B_293] :
      ( k1_funct_1(k2_funct_1(D_292),k1_funct_1(D_292,'#skF_6')) = '#skF_6'
      | k1_xboole_0 = B_293
      | ~ v2_funct_1(D_292)
      | ~ m1_subset_1(D_292,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_293)))
      | ~ v1_funct_2(D_292,'#skF_3',B_293)
      | ~ v1_funct_1(D_292) ) ),
    inference(resolution,[status(thm)],[c_1316,c_1809])).

tff(c_1951,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_1946])).

tff(c_1958,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1313,c_1951])).

tff(c_1959,plain,(
    k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_1945,c_1958])).

tff(c_1944,plain,(
    k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1868])).

tff(c_1969,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1959,c_1944])).

tff(c_1971,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1312,c_1969])).

tff(c_2087,plain,(
    ! [C_306] :
      ( C_306 = '#skF_5'
      | k1_funct_1('#skF_4',C_306) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden(C_306,k1_relat_1('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_1746])).

tff(c_2102,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1472,c_2087])).

tff(c_2119,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_1312,c_2102])).

tff(c_2224,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2145,c_2119])).

tff(c_2226,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2037])).

tff(c_2225,plain,(
    k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2037])).

tff(c_2235,plain,(
    ! [D_311,B_312] :
      ( k1_funct_1(k2_funct_1(D_311),k1_funct_1(D_311,'#skF_5')) = '#skF_5'
      | k1_xboole_0 = B_312
      | ~ v2_funct_1(D_311)
      | ~ m1_subset_1(D_311,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_312)))
      | ~ v1_funct_2(D_311,'#skF_3',B_312)
      | ~ v1_funct_1(D_311) ) ),
    inference(resolution,[status(thm)],[c_1318,c_1990])).

tff(c_2240,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_2235])).

tff(c_2247,plain,
    ( '#skF_5' = '#skF_6'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1313,c_2225,c_1343,c_2240])).

tff(c_2249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2226,c_1312,c_2247])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:45:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.79/1.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.79/1.83  
% 4.79/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.79/1.83  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 4.79/1.83  
% 4.79/1.83  %Foreground sorts:
% 4.79/1.83  
% 4.79/1.83  
% 4.79/1.83  %Background operators:
% 4.79/1.83  
% 4.79/1.83  
% 4.79/1.83  %Foreground operators:
% 4.79/1.83  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.79/1.83  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.79/1.83  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.79/1.83  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.79/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.79/1.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.79/1.83  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.79/1.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.79/1.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.79/1.83  tff('#skF_5', type, '#skF_5': $i).
% 4.79/1.83  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.79/1.83  tff('#skF_6', type, '#skF_6': $i).
% 4.79/1.83  tff('#skF_3', type, '#skF_3': $i).
% 4.79/1.83  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.79/1.83  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.79/1.83  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.79/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.79/1.83  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.79/1.83  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.79/1.83  tff('#skF_4', type, '#skF_4': $i).
% 4.79/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.79/1.83  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.79/1.83  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.79/1.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.79/1.83  
% 4.79/1.85  tff(f_112, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) <=> (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_funct_2)).
% 4.79/1.85  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.79/1.85  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.79/1.85  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 4.79/1.85  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.79/1.85  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_funct_1)).
% 4.79/1.85  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 4.79/1.85  tff(f_94, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_funct_2)).
% 4.79/1.85  tff(f_34, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.79/1.85  tff(c_40, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.79/1.85  tff(c_38, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.79/1.85  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.79/1.85  tff(c_79, plain, (![C_46, A_47, B_48]: (v1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.79/1.85  tff(c_92, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_79])).
% 4.79/1.85  tff(c_141, plain, (![C_63, A_64, B_65]: (v4_relat_1(C_63, A_64) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.79/1.85  tff(c_154, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_141])).
% 4.79/1.85  tff(c_14, plain, (![B_12, A_11]: (r1_tarski(k1_relat_1(B_12), A_11) | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.79/1.85  tff(c_42, plain, ('#skF_5'!='#skF_6' | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.79/1.85  tff(c_61, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_42])).
% 4.79/1.85  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.79/1.85  tff(c_208, plain, (![A_81]: (r2_hidden('#skF_1'(A_81), k1_relat_1(A_81)) | v2_funct_1(A_81) | ~v1_funct_1(A_81) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.79/1.85  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.79/1.85  tff(c_1074, plain, (![A_172, A_173]: (r2_hidden('#skF_1'(A_172), A_173) | ~m1_subset_1(k1_relat_1(A_172), k1_zfmisc_1(A_173)) | v2_funct_1(A_172) | ~v1_funct_1(A_172) | ~v1_relat_1(A_172))), inference(resolution, [status(thm)], [c_208, c_2])).
% 4.79/1.85  tff(c_1276, plain, (![A_191, B_192]: (r2_hidden('#skF_1'(A_191), B_192) | v2_funct_1(A_191) | ~v1_funct_1(A_191) | ~v1_relat_1(A_191) | ~r1_tarski(k1_relat_1(A_191), B_192))), inference(resolution, [status(thm)], [c_8, c_1074])).
% 4.79/1.85  tff(c_189, plain, (![A_72]: ('#skF_2'(A_72)!='#skF_1'(A_72) | v2_funct_1(A_72) | ~v1_funct_1(A_72) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.79/1.85  tff(c_192, plain, ('#skF_2'('#skF_4')!='#skF_1'('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_189, c_61])).
% 4.79/1.85  tff(c_195, plain, ('#skF_2'('#skF_4')!='#skF_1'('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_40, c_192])).
% 4.79/1.85  tff(c_229, plain, (![A_89]: (r2_hidden('#skF_2'(A_89), k1_relat_1(A_89)) | v2_funct_1(A_89) | ~v1_funct_1(A_89) | ~v1_relat_1(A_89))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.79/1.85  tff(c_539, plain, (![A_122, A_123]: (r2_hidden('#skF_2'(A_122), A_123) | ~m1_subset_1(k1_relat_1(A_122), k1_zfmisc_1(A_123)) | v2_funct_1(A_122) | ~v1_funct_1(A_122) | ~v1_relat_1(A_122))), inference(resolution, [status(thm)], [c_229, c_2])).
% 4.79/1.85  tff(c_782, plain, (![A_145, B_146]: (r2_hidden('#skF_2'(A_145), B_146) | v2_funct_1(A_145) | ~v1_funct_1(A_145) | ~v1_relat_1(A_145) | ~r1_tarski(k1_relat_1(A_145), B_146))), inference(resolution, [status(thm)], [c_8, c_539])).
% 4.79/1.85  tff(c_255, plain, (![A_92]: (k1_funct_1(A_92, '#skF_2'(A_92))=k1_funct_1(A_92, '#skF_1'(A_92)) | v2_funct_1(A_92) | ~v1_funct_1(A_92) | ~v1_relat_1(A_92))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.79/1.85  tff(c_60, plain, (![D_37, C_36]: (v2_funct_1('#skF_4') | D_37=C_36 | k1_funct_1('#skF_4', D_37)!=k1_funct_1('#skF_4', C_36) | ~r2_hidden(D_37, '#skF_3') | ~r2_hidden(C_36, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.79/1.85  tff(c_109, plain, (![D_37, C_36]: (D_37=C_36 | k1_funct_1('#skF_4', D_37)!=k1_funct_1('#skF_4', C_36) | ~r2_hidden(D_37, '#skF_3') | ~r2_hidden(C_36, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_61, c_60])).
% 4.79/1.85  tff(c_261, plain, (![C_36]: (C_36='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_36)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | ~r2_hidden(C_36, '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_255, c_109])).
% 4.79/1.85  tff(c_270, plain, (![C_36]: (C_36='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_36)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | ~r2_hidden(C_36, '#skF_3') | v2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_40, c_261])).
% 4.79/1.85  tff(c_271, plain, (![C_36]: (C_36='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_36)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | ~r2_hidden(C_36, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_61, c_270])).
% 4.79/1.85  tff(c_374, plain, (~r2_hidden('#skF_2'('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_271])).
% 4.79/1.85  tff(c_787, plain, (v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_782, c_374])).
% 4.79/1.85  tff(c_801, plain, (v2_funct_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_40, c_787])).
% 4.79/1.85  tff(c_802, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_61, c_801])).
% 4.79/1.85  tff(c_809, plain, (~v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_802])).
% 4.79/1.85  tff(c_813, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_154, c_809])).
% 4.79/1.85  tff(c_815, plain, (r2_hidden('#skF_2'('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_271])).
% 4.79/1.85  tff(c_264, plain, (![D_37]: (D_37='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_37)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_37, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_255, c_109])).
% 4.79/1.85  tff(c_273, plain, (![D_37]: (D_37='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_37)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_37, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_40, c_264])).
% 4.79/1.85  tff(c_274, plain, (![D_37]: (D_37='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_37)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_37, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_61, c_273])).
% 4.79/1.85  tff(c_872, plain, (![D_37]: (D_37='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_37)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_37, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_815, c_274])).
% 4.79/1.85  tff(c_875, plain, ('#skF_2'('#skF_4')='#skF_1'('#skF_4') | ~r2_hidden('#skF_1'('#skF_4'), '#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_872])).
% 4.79/1.85  tff(c_876, plain, (~r2_hidden('#skF_1'('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_195, c_875])).
% 4.79/1.85  tff(c_1284, plain, (v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_1276, c_876])).
% 4.79/1.85  tff(c_1299, plain, (v2_funct_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_40, c_1284])).
% 4.79/1.85  tff(c_1300, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_61, c_1299])).
% 4.79/1.85  tff(c_1307, plain, (~v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_1300])).
% 4.79/1.85  tff(c_1311, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_154, c_1307])).
% 4.79/1.85  tff(c_1313, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_42])).
% 4.79/1.85  tff(c_46, plain, (r2_hidden('#skF_6', '#skF_3') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.79/1.85  tff(c_1316, plain, (r2_hidden('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1313, c_46])).
% 4.79/1.85  tff(c_1990, plain, (![D_294, C_295, B_296, A_297]: (k1_funct_1(k2_funct_1(D_294), k1_funct_1(D_294, C_295))=C_295 | k1_xboole_0=B_296 | ~r2_hidden(C_295, A_297) | ~v2_funct_1(D_294) | ~m1_subset_1(D_294, k1_zfmisc_1(k2_zfmisc_1(A_297, B_296))) | ~v1_funct_2(D_294, A_297, B_296) | ~v1_funct_1(D_294))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.79/1.85  tff(c_2025, plain, (![D_300, B_301]: (k1_funct_1(k2_funct_1(D_300), k1_funct_1(D_300, '#skF_6'))='#skF_6' | k1_xboole_0=B_301 | ~v2_funct_1(D_300) | ~m1_subset_1(D_300, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_301))) | ~v1_funct_2(D_300, '#skF_3', B_301) | ~v1_funct_1(D_300))), inference(resolution, [status(thm)], [c_1316, c_1990])).
% 4.79/1.85  tff(c_2030, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_2025])).
% 4.79/1.85  tff(c_2037, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_1313, c_2030])).
% 4.79/1.85  tff(c_2125, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_2037])).
% 4.79/1.85  tff(c_4, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.79/1.85  tff(c_1329, plain, (![A_198, B_199]: (r1_tarski(A_198, B_199) | ~m1_subset_1(A_198, k1_zfmisc_1(B_199)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.79/1.85  tff(c_1341, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(resolution, [status(thm)], [c_4, c_1329])).
% 4.79/1.85  tff(c_2145, plain, (![A_5]: (r1_tarski('#skF_3', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_2125, c_1341])).
% 4.79/1.85  tff(c_1312, plain, ('#skF_5'!='#skF_6'), inference(splitRight, [status(thm)], [c_42])).
% 4.79/1.85  tff(c_1435, plain, (![C_221, A_222, B_223]: (r2_hidden(C_221, A_222) | ~r2_hidden(C_221, B_223) | ~m1_subset_1(B_223, k1_zfmisc_1(A_222)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.79/1.85  tff(c_1467, plain, (![A_228]: (r2_hidden('#skF_6', A_228) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_228)))), inference(resolution, [status(thm)], [c_1316, c_1435])).
% 4.79/1.85  tff(c_1472, plain, (![B_7]: (r2_hidden('#skF_6', B_7) | ~r1_tarski('#skF_3', B_7))), inference(resolution, [status(thm)], [c_8, c_1467])).
% 4.79/1.85  tff(c_44, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.79/1.85  tff(c_1343, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1313, c_44])).
% 4.79/1.85  tff(c_48, plain, (r2_hidden('#skF_5', '#skF_3') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.79/1.85  tff(c_1318, plain, (r2_hidden('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1313, c_48])).
% 4.79/1.85  tff(c_1809, plain, (![D_282, C_283, B_284, A_285]: (k1_funct_1(k2_funct_1(D_282), k1_funct_1(D_282, C_283))=C_283 | k1_xboole_0=B_284 | ~r2_hidden(C_283, A_285) | ~v2_funct_1(D_282) | ~m1_subset_1(D_282, k1_zfmisc_1(k2_zfmisc_1(A_285, B_284))) | ~v1_funct_2(D_282, A_285, B_284) | ~v1_funct_1(D_282))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.79/1.85  tff(c_1856, plain, (![D_287, B_288]: (k1_funct_1(k2_funct_1(D_287), k1_funct_1(D_287, '#skF_5'))='#skF_5' | k1_xboole_0=B_288 | ~v2_funct_1(D_287) | ~m1_subset_1(D_287, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_288))) | ~v1_funct_2(D_287, '#skF_3', B_288) | ~v1_funct_1(D_287))), inference(resolution, [status(thm)], [c_1318, c_1809])).
% 4.79/1.85  tff(c_1861, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_5'))='#skF_5' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_1856])).
% 4.79/1.85  tff(c_1868, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_5' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_1313, c_1343, c_1861])).
% 4.79/1.85  tff(c_1870, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1868])).
% 4.79/1.85  tff(c_1892, plain, (![A_5]: (r1_tarski('#skF_3', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_1870, c_1341])).
% 4.79/1.85  tff(c_1443, plain, (![A_225]: (r2_hidden('#skF_5', A_225) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_225)))), inference(resolution, [status(thm)], [c_1318, c_1435])).
% 4.79/1.85  tff(c_1448, plain, (![B_7]: (r2_hidden('#skF_5', B_7) | ~r1_tarski('#skF_3', B_7))), inference(resolution, [status(thm)], [c_8, c_1443])).
% 4.79/1.85  tff(c_1349, plain, (![C_201, A_202, B_203]: (v1_relat_1(C_201) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(A_202, B_203))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.79/1.85  tff(c_1362, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_1349])).
% 4.79/1.85  tff(c_1734, plain, (![C_277, B_278, A_279]: (C_277=B_278 | k1_funct_1(A_279, C_277)!=k1_funct_1(A_279, B_278) | ~r2_hidden(C_277, k1_relat_1(A_279)) | ~r2_hidden(B_278, k1_relat_1(A_279)) | ~v2_funct_1(A_279) | ~v1_funct_1(A_279) | ~v1_relat_1(A_279))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.79/1.85  tff(c_1742, plain, (![C_277]: (C_277='#skF_5' | k1_funct_1('#skF_4', C_277)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden(C_277, k1_relat_1('#skF_4')) | ~r2_hidden('#skF_5', k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1343, c_1734])).
% 4.79/1.85  tff(c_1746, plain, (![C_277]: (C_277='#skF_5' | k1_funct_1('#skF_4', C_277)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden(C_277, k1_relat_1('#skF_4')) | ~r2_hidden('#skF_5', k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1362, c_40, c_1313, c_1742])).
% 4.79/1.85  tff(c_1775, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_1746])).
% 4.79/1.85  tff(c_1779, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1448, c_1775])).
% 4.79/1.85  tff(c_1943, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1892, c_1779])).
% 4.79/1.85  tff(c_1945, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_1868])).
% 4.79/1.85  tff(c_1946, plain, (![D_292, B_293]: (k1_funct_1(k2_funct_1(D_292), k1_funct_1(D_292, '#skF_6'))='#skF_6' | k1_xboole_0=B_293 | ~v2_funct_1(D_292) | ~m1_subset_1(D_292, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_293))) | ~v1_funct_2(D_292, '#skF_3', B_293) | ~v1_funct_1(D_292))), inference(resolution, [status(thm)], [c_1316, c_1809])).
% 4.79/1.85  tff(c_1951, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_1946])).
% 4.79/1.85  tff(c_1958, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_1313, c_1951])).
% 4.79/1.85  tff(c_1959, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_1945, c_1958])).
% 4.79/1.85  tff(c_1944, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_1868])).
% 4.79/1.85  tff(c_1969, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1959, c_1944])).
% 4.79/1.85  tff(c_1971, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1312, c_1969])).
% 4.79/1.85  tff(c_2087, plain, (![C_306]: (C_306='#skF_5' | k1_funct_1('#skF_4', C_306)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden(C_306, k1_relat_1('#skF_4')))), inference(splitRight, [status(thm)], [c_1746])).
% 4.79/1.85  tff(c_2102, plain, ('#skF_5'='#skF_6' | ~r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1472, c_2087])).
% 4.79/1.85  tff(c_2119, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1312, c_2102])).
% 4.79/1.85  tff(c_2224, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2145, c_2119])).
% 4.79/1.85  tff(c_2226, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_2037])).
% 4.79/1.85  tff(c_2225, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_2037])).
% 4.79/1.85  tff(c_2235, plain, (![D_311, B_312]: (k1_funct_1(k2_funct_1(D_311), k1_funct_1(D_311, '#skF_5'))='#skF_5' | k1_xboole_0=B_312 | ~v2_funct_1(D_311) | ~m1_subset_1(D_311, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_312))) | ~v1_funct_2(D_311, '#skF_3', B_312) | ~v1_funct_1(D_311))), inference(resolution, [status(thm)], [c_1318, c_1990])).
% 4.79/1.85  tff(c_2240, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_5'))='#skF_5' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_2235])).
% 4.79/1.85  tff(c_2247, plain, ('#skF_5'='#skF_6' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_1313, c_2225, c_1343, c_2240])).
% 4.79/1.85  tff(c_2249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2226, c_1312, c_2247])).
% 4.79/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.79/1.85  
% 4.79/1.85  Inference rules
% 4.79/1.85  ----------------------
% 4.79/1.85  #Ref     : 5
% 4.79/1.85  #Sup     : 376
% 4.79/1.85  #Fact    : 0
% 4.79/1.85  #Define  : 0
% 4.79/1.85  #Split   : 22
% 4.79/1.85  #Chain   : 0
% 4.79/1.85  #Close   : 0
% 4.79/1.85  
% 4.79/1.85  Ordering : KBO
% 4.79/1.85  
% 4.79/1.85  Simplification rules
% 4.79/1.85  ----------------------
% 4.79/1.85  #Subsume      : 52
% 4.79/1.85  #Demod        : 275
% 4.79/1.85  #Tautology    : 51
% 4.79/1.85  #SimpNegUnit  : 11
% 4.79/1.85  #BackRed      : 83
% 4.79/1.85  
% 4.79/1.85  #Partial instantiations: 0
% 4.79/1.85  #Strategies tried      : 1
% 4.79/1.85  
% 4.79/1.85  Timing (in seconds)
% 4.79/1.85  ----------------------
% 4.79/1.86  Preprocessing        : 0.34
% 4.79/1.86  Parsing              : 0.18
% 4.79/1.86  CNF conversion       : 0.02
% 4.79/1.86  Main loop            : 0.73
% 4.79/1.86  Inferencing          : 0.27
% 4.79/1.86  Reduction            : 0.23
% 4.79/1.86  Demodulation         : 0.15
% 4.79/1.86  BG Simplification    : 0.03
% 4.79/1.86  Subsumption          : 0.14
% 4.79/1.86  Abstraction          : 0.03
% 4.79/1.86  MUC search           : 0.00
% 4.79/1.86  Cooper               : 0.00
% 4.79/1.86  Total                : 1.12
% 4.79/1.86  Index Insertion      : 0.00
% 4.79/1.86  Index Deletion       : 0.00
% 4.79/1.86  Index Matching       : 0.00
% 4.79/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
