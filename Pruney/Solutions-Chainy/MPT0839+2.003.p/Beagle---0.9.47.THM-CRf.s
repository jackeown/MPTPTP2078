%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:22 EST 2020

% Result     : Theorem 4.19s
% Output     : CNFRefutation 4.19s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 442 expanded)
%              Number of leaves         :   39 ( 160 expanded)
%              Depth                    :   15
%              Number of atoms          :  219 ( 835 expanded)
%              Number of equality atoms :   43 ( 147 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_117,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_37,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2006,plain,(
    ! [A_264,B_265,C_266] :
      ( k2_relset_1(A_264,B_265,C_266) = k2_relat_1(C_266)
      | ~ m1_subset_1(C_266,k1_zfmisc_1(k2_zfmisc_1(A_264,B_265))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2030,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_2006])).

tff(c_44,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2032,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2030,c_44])).

tff(c_8,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_7] : m1_subset_1(k2_subset_1(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_51,plain,(
    ! [A_7] : m1_subset_1(A_7,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_104,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(A_64,B_65)
      | ~ m1_subset_1(A_64,k1_zfmisc_1(B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_121,plain,(
    ! [A_7] : r1_tarski(A_7,A_7) ),
    inference(resolution,[status(thm)],[c_51,c_104])).

tff(c_159,plain,(
    ! [C_72,A_73,B_74] :
      ( v1_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_178,plain,(
    ! [A_73,B_74] : v1_relat_1(k2_zfmisc_1(A_73,B_74)) ),
    inference(resolution,[status(thm)],[c_51,c_159])).

tff(c_202,plain,(
    ! [C_83,A_84,B_85] :
      ( v4_relat_1(C_83,A_84)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_221,plain,(
    ! [A_84,B_85] : v4_relat_1(k2_zfmisc_1(A_84,B_85),A_84) ),
    inference(resolution,[status(thm)],[c_51,c_202])).

tff(c_243,plain,(
    ! [B_93,A_94] :
      ( k7_relat_1(B_93,A_94) = B_93
      | ~ v4_relat_1(B_93,A_94)
      | ~ v1_relat_1(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_249,plain,(
    ! [A_84,B_85] :
      ( k7_relat_1(k2_zfmisc_1(A_84,B_85),A_84) = k2_zfmisc_1(A_84,B_85)
      | ~ v1_relat_1(k2_zfmisc_1(A_84,B_85)) ) ),
    inference(resolution,[status(thm)],[c_221,c_243])).

tff(c_258,plain,(
    ! [A_84,B_85] : k7_relat_1(k2_zfmisc_1(A_84,B_85),A_84) = k2_zfmisc_1(A_84,B_85) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_249])).

tff(c_18,plain,(
    ! [A_12] :
      ( v1_xboole_0(k2_relat_1(A_12))
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_64,plain,(
    ! [A_55] :
      ( v1_xboole_0(k2_relat_1(A_55))
      | ~ v1_xboole_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_69,plain,(
    ! [A_56] :
      ( k2_relat_1(A_56) = k1_xboole_0
      | ~ v1_xboole_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_64,c_6])).

tff(c_85,plain,(
    ! [A_61] :
      ( k2_relat_1(k2_relat_1(A_61)) = k1_xboole_0
      | ~ v1_xboole_0(A_61) ) ),
    inference(resolution,[status(thm)],[c_18,c_69])).

tff(c_94,plain,(
    ! [A_61] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(k2_relat_1(A_61))
      | ~ v1_xboole_0(A_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_18])).

tff(c_130,plain,(
    ! [A_68] :
      ( ~ v1_xboole_0(k2_relat_1(A_68))
      | ~ v1_xboole_0(A_68) ) ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_137,plain,(
    ! [A_12] : ~ v1_xboole_0(A_12) ),
    inference(resolution,[status(thm)],[c_18,c_130])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_139,plain,(
    ! [A_1] : r2_hidden('#skF_1'(A_1),A_1) ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_4])).

tff(c_298,plain,(
    ! [A_104,B_105,C_106] :
      ( r2_hidden(A_104,B_105)
      | ~ r2_hidden(A_104,k1_relat_1(k7_relat_1(C_106,B_105)))
      | ~ v1_relat_1(C_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_342,plain,(
    ! [C_111,B_112] :
      ( r2_hidden('#skF_1'(k1_relat_1(k7_relat_1(C_111,B_112))),B_112)
      | ~ v1_relat_1(C_111) ) ),
    inference(resolution,[status(thm)],[c_139,c_298])).

tff(c_360,plain,(
    ! [A_84,B_85] :
      ( r2_hidden('#skF_1'(k1_relat_1(k2_zfmisc_1(A_84,B_85))),A_84)
      | ~ v1_relat_1(k2_zfmisc_1(A_84,B_85)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_342])).

tff(c_397,plain,(
    ! [A_116,B_117] : r2_hidden('#skF_1'(k1_relat_1(k2_zfmisc_1(A_116,B_117))),A_116) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_360])).

tff(c_177,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_159])).

tff(c_220,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_202])).

tff(c_252,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_220,c_243])).

tff(c_261,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_252])).

tff(c_304,plain,(
    ! [A_104] :
      ( r2_hidden(A_104,'#skF_3')
      | ~ r2_hidden(A_104,k1_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_298])).

tff(c_312,plain,(
    ! [A_104] :
      ( r2_hidden(A_104,'#skF_3')
      | ~ r2_hidden(A_104,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_304])).

tff(c_444,plain,(
    ! [B_121] : r2_hidden('#skF_1'(k1_relat_1(k2_zfmisc_1(k1_relat_1('#skF_4'),B_121))),'#skF_3') ),
    inference(resolution,[status(thm)],[c_397,c_312])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,B_9)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_448,plain,(
    ! [B_121] : m1_subset_1('#skF_1'(k1_relat_1(k2_zfmisc_1(k1_relat_1('#skF_4'),B_121))),'#skF_3') ),
    inference(resolution,[status(thm)],[c_444,c_12])).

tff(c_502,plain,(
    ! [A_127,B_128,C_129] :
      ( k1_relset_1(A_127,B_128,C_129) = k1_relat_1(C_129)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_530,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_502])).

tff(c_42,plain,(
    ! [D_49] :
      ( ~ r2_hidden(D_49,k1_relset_1('#skF_3','#skF_2','#skF_4'))
      | ~ m1_subset_1(D_49,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_415,plain,(
    ! [B_117] : ~ m1_subset_1('#skF_1'(k1_relat_1(k2_zfmisc_1(k1_relset_1('#skF_3','#skF_2','#skF_4'),B_117))),'#skF_3') ),
    inference(resolution,[status(thm)],[c_397,c_42])).

tff(c_532,plain,(
    ! [B_117] : ~ m1_subset_1('#skF_1'(k1_relat_1(k2_zfmisc_1(k1_relat_1('#skF_4'),B_117))),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_530,c_415])).

tff(c_537,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_532])).

tff(c_538,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_1636,plain,(
    ! [C_231,A_232,B_233] :
      ( v1_xboole_0(C_231)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1(A_232,B_233)))
      | ~ v1_xboole_0(A_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1656,plain,(
    ! [A_234,B_235] :
      ( v1_xboole_0(k2_zfmisc_1(A_234,B_235))
      | ~ v1_xboole_0(A_234) ) ),
    inference(resolution,[status(thm)],[c_51,c_1636])).

tff(c_1665,plain,(
    ! [A_236,B_237] :
      ( k2_zfmisc_1(A_236,B_237) = k1_xboole_0
      | ~ v1_xboole_0(A_236) ) ),
    inference(resolution,[status(thm)],[c_1656,c_6])).

tff(c_1673,plain,(
    ! [B_237] : k2_zfmisc_1(k1_xboole_0,B_237) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_538,c_1665])).

tff(c_880,plain,(
    ! [A_178,B_179,C_180] :
      ( k2_relset_1(A_178,B_179,C_180) = k2_relat_1(C_180)
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_178,B_179))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_901,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_880])).

tff(c_903,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_901,c_44])).

tff(c_703,plain,(
    ! [C_158,A_159,B_160] :
      ( v1_xboole_0(C_158)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160)))
      | ~ v1_xboole_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_723,plain,(
    ! [A_161,B_162] :
      ( v1_xboole_0(k2_zfmisc_1(A_161,B_162))
      | ~ v1_xboole_0(A_161) ) ),
    inference(resolution,[status(thm)],[c_51,c_703])).

tff(c_732,plain,(
    ! [A_163,B_164] :
      ( k2_zfmisc_1(A_163,B_164) = k1_xboole_0
      | ~ v1_xboole_0(A_163) ) ),
    inference(resolution,[status(thm)],[c_723,c_6])).

tff(c_740,plain,(
    ! [B_164] : k2_zfmisc_1(k1_xboole_0,B_164) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_538,c_732])).

tff(c_568,plain,(
    ! [C_131,A_132,B_133] :
      ( v1_relat_1(C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_586,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_568])).

tff(c_607,plain,(
    ! [C_140,A_141,B_142] :
      ( v4_relat_1(C_140,A_141)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_625,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_607])).

tff(c_648,plain,(
    ! [B_148,A_149] :
      ( k7_relat_1(B_148,A_149) = B_148
      | ~ v4_relat_1(B_148,A_149)
      | ~ v1_relat_1(B_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_654,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_625,c_648])).

tff(c_660,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_654])).

tff(c_784,plain,(
    ! [A_167,B_168,C_169] :
      ( r2_hidden(A_167,B_168)
      | ~ r2_hidden(A_167,k1_relat_1(k7_relat_1(C_169,B_168)))
      | ~ v1_relat_1(C_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_787,plain,(
    ! [A_167] :
      ( r2_hidden(A_167,'#skF_3')
      | ~ r2_hidden(A_167,k1_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_660,c_784])).

tff(c_822,plain,(
    ! [A_171] :
      ( r2_hidden(A_171,'#skF_3')
      | ~ r2_hidden(A_171,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_787])).

tff(c_827,plain,
    ( r2_hidden('#skF_1'(k1_relat_1('#skF_4')),'#skF_3')
    | v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_4,c_822])).

tff(c_930,plain,(
    v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_827])).

tff(c_941,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_930,c_6])).

tff(c_1400,plain,(
    ! [D_215,B_216,C_217,A_218] :
      ( m1_subset_1(D_215,k1_zfmisc_1(k2_zfmisc_1(B_216,C_217)))
      | ~ r1_tarski(k1_relat_1(D_215),B_216)
      | ~ m1_subset_1(D_215,k1_zfmisc_1(k2_zfmisc_1(A_218,C_217))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1412,plain,(
    ! [B_216] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_216,'#skF_2')))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_216) ) ),
    inference(resolution,[status(thm)],[c_46,c_1400])).

tff(c_1453,plain,(
    ! [B_219] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_219,'#skF_2')))
      | ~ r1_tarski(k1_xboole_0,B_219) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_941,c_1412])).

tff(c_1484,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_740,c_1453])).

tff(c_1498,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_1484])).

tff(c_742,plain,(
    ! [B_165] : k2_zfmisc_1(k1_xboole_0,B_165) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_538,c_732])).

tff(c_34,plain,(
    ! [C_27,A_24,B_25] :
      ( v1_xboole_0(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25)))
      | ~ v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_750,plain,(
    ! [C_27] :
      ( v1_xboole_0(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_742,c_34])).

tff(c_781,plain,(
    ! [C_27] :
      ( v1_xboole_0(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_538,c_750])).

tff(c_1515,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1498,c_781])).

tff(c_68,plain,(
    ! [A_55] :
      ( k2_relat_1(A_55) = k1_xboole_0
      | ~ v1_xboole_0(A_55) ) ),
    inference(resolution,[status(thm)],[c_64,c_6])).

tff(c_1523,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1515,c_68])).

tff(c_1531,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_903,c_1523])).

tff(c_1532,plain,(
    r2_hidden('#skF_1'(k1_relat_1('#skF_4')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_827])).

tff(c_1540,plain,(
    m1_subset_1('#skF_1'(k1_relat_1('#skF_4')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1532,c_12])).

tff(c_1542,plain,(
    ! [A_220,B_221,C_222] :
      ( k1_relset_1(A_220,B_221,C_222) = k1_relat_1(C_222)
      | ~ m1_subset_1(C_222,k1_zfmisc_1(k2_zfmisc_1(A_220,B_221))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1563,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_1542])).

tff(c_562,plain,(
    ! [D_130] :
      ( ~ r2_hidden(D_130,k1_relset_1('#skF_3','#skF_2','#skF_4'))
      | ~ m1_subset_1(D_130,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_567,plain,
    ( ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_3','#skF_2','#skF_4')),'#skF_3')
    | v1_xboole_0(k1_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_4,c_562])).

tff(c_645,plain,(
    ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_3','#skF_2','#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_567])).

tff(c_1565,plain,(
    ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1563,c_645])).

tff(c_1569,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1540,c_1565])).

tff(c_1570,plain,(
    v1_xboole_0(k1_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_567])).

tff(c_1579,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1570,c_6])).

tff(c_1831,plain,(
    ! [A_251,B_252,C_253] :
      ( k1_relset_1(A_251,B_252,C_253) = k1_relat_1(C_253)
      | ~ m1_subset_1(C_253,k1_zfmisc_1(k2_zfmisc_1(A_251,B_252))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1845,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_1831])).

tff(c_1853,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1579,c_1845])).

tff(c_2471,plain,(
    ! [D_301,B_302,C_303,A_304] :
      ( m1_subset_1(D_301,k1_zfmisc_1(k2_zfmisc_1(B_302,C_303)))
      | ~ r1_tarski(k1_relat_1(D_301),B_302)
      | ~ m1_subset_1(D_301,k1_zfmisc_1(k2_zfmisc_1(A_304,C_303))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2483,plain,(
    ! [B_302] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_302,'#skF_2')))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_302) ) ),
    inference(resolution,[status(thm)],[c_46,c_2471])).

tff(c_2617,plain,(
    ! [B_312] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_312,'#skF_2')))
      | ~ r1_tarski(k1_xboole_0,B_312) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1853,c_2483])).

tff(c_2652,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1673,c_2617])).

tff(c_2666,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_2652])).

tff(c_1675,plain,(
    ! [B_238] : k2_zfmisc_1(k1_xboole_0,B_238) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_538,c_1665])).

tff(c_1683,plain,(
    ! [C_27] :
      ( v1_xboole_0(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1675,c_34])).

tff(c_1711,plain,(
    ! [C_27] :
      ( v1_xboole_0(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_538,c_1683])).

tff(c_2683,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_2666,c_1711])).

tff(c_2691,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2683,c_68])).

tff(c_2699,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2032,c_2691])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:22:54 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.19/1.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.19/1.86  
% 4.19/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.19/1.86  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 4.19/1.86  
% 4.19/1.86  %Foreground sorts:
% 4.19/1.86  
% 4.19/1.86  
% 4.19/1.86  %Background operators:
% 4.19/1.86  
% 4.19/1.86  
% 4.19/1.86  %Foreground operators:
% 4.19/1.86  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.19/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.19/1.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.19/1.86  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.19/1.86  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.19/1.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.19/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.19/1.86  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.19/1.86  tff('#skF_2', type, '#skF_2': $i).
% 4.19/1.86  tff('#skF_3', type, '#skF_3': $i).
% 4.19/1.86  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.19/1.86  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.19/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.19/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.19/1.86  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.19/1.86  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.19/1.86  tff('#skF_4', type, '#skF_4': $i).
% 4.19/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.19/1.86  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.19/1.86  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.19/1.86  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.19/1.86  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.19/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.19/1.86  
% 4.19/1.89  tff(f_117, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relset_1)).
% 4.19/1.89  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.19/1.89  tff(f_37, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.19/1.89  tff(f_39, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.19/1.89  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.19/1.89  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.19/1.89  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.19/1.89  tff(f_57, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 4.19/1.89  tff(f_51, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc11_relat_1)).
% 4.19/1.89  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.19/1.89  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.19/1.89  tff(f_65, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 4.19/1.89  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 4.19/1.89  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.19/1.89  tff(f_82, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 4.19/1.89  tff(f_96, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 4.19/1.89  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.19/1.89  tff(c_2006, plain, (![A_264, B_265, C_266]: (k2_relset_1(A_264, B_265, C_266)=k2_relat_1(C_266) | ~m1_subset_1(C_266, k1_zfmisc_1(k2_zfmisc_1(A_264, B_265))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.19/1.89  tff(c_2030, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_2006])).
% 4.19/1.89  tff(c_44, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.19/1.89  tff(c_2032, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2030, c_44])).
% 4.19/1.89  tff(c_8, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.19/1.89  tff(c_10, plain, (![A_7]: (m1_subset_1(k2_subset_1(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.19/1.89  tff(c_51, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 4.19/1.89  tff(c_104, plain, (![A_64, B_65]: (r1_tarski(A_64, B_65) | ~m1_subset_1(A_64, k1_zfmisc_1(B_65)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.19/1.89  tff(c_121, plain, (![A_7]: (r1_tarski(A_7, A_7))), inference(resolution, [status(thm)], [c_51, c_104])).
% 4.19/1.89  tff(c_159, plain, (![C_72, A_73, B_74]: (v1_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.19/1.89  tff(c_178, plain, (![A_73, B_74]: (v1_relat_1(k2_zfmisc_1(A_73, B_74)))), inference(resolution, [status(thm)], [c_51, c_159])).
% 4.19/1.89  tff(c_202, plain, (![C_83, A_84, B_85]: (v4_relat_1(C_83, A_84) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.19/1.89  tff(c_221, plain, (![A_84, B_85]: (v4_relat_1(k2_zfmisc_1(A_84, B_85), A_84))), inference(resolution, [status(thm)], [c_51, c_202])).
% 4.19/1.89  tff(c_243, plain, (![B_93, A_94]: (k7_relat_1(B_93, A_94)=B_93 | ~v4_relat_1(B_93, A_94) | ~v1_relat_1(B_93))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.19/1.89  tff(c_249, plain, (![A_84, B_85]: (k7_relat_1(k2_zfmisc_1(A_84, B_85), A_84)=k2_zfmisc_1(A_84, B_85) | ~v1_relat_1(k2_zfmisc_1(A_84, B_85)))), inference(resolution, [status(thm)], [c_221, c_243])).
% 4.19/1.89  tff(c_258, plain, (![A_84, B_85]: (k7_relat_1(k2_zfmisc_1(A_84, B_85), A_84)=k2_zfmisc_1(A_84, B_85))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_249])).
% 4.19/1.89  tff(c_18, plain, (![A_12]: (v1_xboole_0(k2_relat_1(A_12)) | ~v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.19/1.89  tff(c_64, plain, (![A_55]: (v1_xboole_0(k2_relat_1(A_55)) | ~v1_xboole_0(A_55))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.19/1.89  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.19/1.89  tff(c_69, plain, (![A_56]: (k2_relat_1(A_56)=k1_xboole_0 | ~v1_xboole_0(A_56))), inference(resolution, [status(thm)], [c_64, c_6])).
% 4.19/1.89  tff(c_85, plain, (![A_61]: (k2_relat_1(k2_relat_1(A_61))=k1_xboole_0 | ~v1_xboole_0(A_61))), inference(resolution, [status(thm)], [c_18, c_69])).
% 4.19/1.89  tff(c_94, plain, (![A_61]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k2_relat_1(A_61)) | ~v1_xboole_0(A_61))), inference(superposition, [status(thm), theory('equality')], [c_85, c_18])).
% 4.19/1.89  tff(c_130, plain, (![A_68]: (~v1_xboole_0(k2_relat_1(A_68)) | ~v1_xboole_0(A_68))), inference(splitLeft, [status(thm)], [c_94])).
% 4.19/1.89  tff(c_137, plain, (![A_12]: (~v1_xboole_0(A_12))), inference(resolution, [status(thm)], [c_18, c_130])).
% 4.19/1.89  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.19/1.89  tff(c_139, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1))), inference(negUnitSimplification, [status(thm)], [c_137, c_4])).
% 4.19/1.89  tff(c_298, plain, (![A_104, B_105, C_106]: (r2_hidden(A_104, B_105) | ~r2_hidden(A_104, k1_relat_1(k7_relat_1(C_106, B_105))) | ~v1_relat_1(C_106))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.19/1.89  tff(c_342, plain, (![C_111, B_112]: (r2_hidden('#skF_1'(k1_relat_1(k7_relat_1(C_111, B_112))), B_112) | ~v1_relat_1(C_111))), inference(resolution, [status(thm)], [c_139, c_298])).
% 4.19/1.89  tff(c_360, plain, (![A_84, B_85]: (r2_hidden('#skF_1'(k1_relat_1(k2_zfmisc_1(A_84, B_85))), A_84) | ~v1_relat_1(k2_zfmisc_1(A_84, B_85)))), inference(superposition, [status(thm), theory('equality')], [c_258, c_342])).
% 4.19/1.89  tff(c_397, plain, (![A_116, B_117]: (r2_hidden('#skF_1'(k1_relat_1(k2_zfmisc_1(A_116, B_117))), A_116))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_360])).
% 4.19/1.89  tff(c_177, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_159])).
% 4.19/1.89  tff(c_220, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_202])).
% 4.19/1.89  tff(c_252, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_220, c_243])).
% 4.19/1.89  tff(c_261, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_177, c_252])).
% 4.19/1.89  tff(c_304, plain, (![A_104]: (r2_hidden(A_104, '#skF_3') | ~r2_hidden(A_104, k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_261, c_298])).
% 4.19/1.89  tff(c_312, plain, (![A_104]: (r2_hidden(A_104, '#skF_3') | ~r2_hidden(A_104, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_304])).
% 4.19/1.89  tff(c_444, plain, (![B_121]: (r2_hidden('#skF_1'(k1_relat_1(k2_zfmisc_1(k1_relat_1('#skF_4'), B_121))), '#skF_3'))), inference(resolution, [status(thm)], [c_397, c_312])).
% 4.19/1.89  tff(c_12, plain, (![A_8, B_9]: (m1_subset_1(A_8, B_9) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.19/1.89  tff(c_448, plain, (![B_121]: (m1_subset_1('#skF_1'(k1_relat_1(k2_zfmisc_1(k1_relat_1('#skF_4'), B_121))), '#skF_3'))), inference(resolution, [status(thm)], [c_444, c_12])).
% 4.19/1.89  tff(c_502, plain, (![A_127, B_128, C_129]: (k1_relset_1(A_127, B_128, C_129)=k1_relat_1(C_129) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.19/1.89  tff(c_530, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_502])).
% 4.19/1.89  tff(c_42, plain, (![D_49]: (~r2_hidden(D_49, k1_relset_1('#skF_3', '#skF_2', '#skF_4')) | ~m1_subset_1(D_49, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.19/1.89  tff(c_415, plain, (![B_117]: (~m1_subset_1('#skF_1'(k1_relat_1(k2_zfmisc_1(k1_relset_1('#skF_3', '#skF_2', '#skF_4'), B_117))), '#skF_3'))), inference(resolution, [status(thm)], [c_397, c_42])).
% 4.19/1.89  tff(c_532, plain, (![B_117]: (~m1_subset_1('#skF_1'(k1_relat_1(k2_zfmisc_1(k1_relat_1('#skF_4'), B_117))), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_530, c_415])).
% 4.19/1.89  tff(c_537, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_448, c_532])).
% 4.19/1.89  tff(c_538, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_94])).
% 4.19/1.89  tff(c_1636, plain, (![C_231, A_232, B_233]: (v1_xboole_0(C_231) | ~m1_subset_1(C_231, k1_zfmisc_1(k2_zfmisc_1(A_232, B_233))) | ~v1_xboole_0(A_232))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.19/1.89  tff(c_1656, plain, (![A_234, B_235]: (v1_xboole_0(k2_zfmisc_1(A_234, B_235)) | ~v1_xboole_0(A_234))), inference(resolution, [status(thm)], [c_51, c_1636])).
% 4.19/1.89  tff(c_1665, plain, (![A_236, B_237]: (k2_zfmisc_1(A_236, B_237)=k1_xboole_0 | ~v1_xboole_0(A_236))), inference(resolution, [status(thm)], [c_1656, c_6])).
% 4.19/1.89  tff(c_1673, plain, (![B_237]: (k2_zfmisc_1(k1_xboole_0, B_237)=k1_xboole_0)), inference(resolution, [status(thm)], [c_538, c_1665])).
% 4.19/1.89  tff(c_880, plain, (![A_178, B_179, C_180]: (k2_relset_1(A_178, B_179, C_180)=k2_relat_1(C_180) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_178, B_179))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.19/1.89  tff(c_901, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_880])).
% 4.19/1.89  tff(c_903, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_901, c_44])).
% 4.19/1.89  tff(c_703, plain, (![C_158, A_159, B_160]: (v1_xboole_0(C_158) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))) | ~v1_xboole_0(A_159))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.19/1.89  tff(c_723, plain, (![A_161, B_162]: (v1_xboole_0(k2_zfmisc_1(A_161, B_162)) | ~v1_xboole_0(A_161))), inference(resolution, [status(thm)], [c_51, c_703])).
% 4.19/1.89  tff(c_732, plain, (![A_163, B_164]: (k2_zfmisc_1(A_163, B_164)=k1_xboole_0 | ~v1_xboole_0(A_163))), inference(resolution, [status(thm)], [c_723, c_6])).
% 4.19/1.89  tff(c_740, plain, (![B_164]: (k2_zfmisc_1(k1_xboole_0, B_164)=k1_xboole_0)), inference(resolution, [status(thm)], [c_538, c_732])).
% 4.19/1.89  tff(c_568, plain, (![C_131, A_132, B_133]: (v1_relat_1(C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.19/1.89  tff(c_586, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_568])).
% 4.19/1.89  tff(c_607, plain, (![C_140, A_141, B_142]: (v4_relat_1(C_140, A_141) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.19/1.89  tff(c_625, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_607])).
% 4.19/1.89  tff(c_648, plain, (![B_148, A_149]: (k7_relat_1(B_148, A_149)=B_148 | ~v4_relat_1(B_148, A_149) | ~v1_relat_1(B_148))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.19/1.89  tff(c_654, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_625, c_648])).
% 4.19/1.89  tff(c_660, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_586, c_654])).
% 4.19/1.89  tff(c_784, plain, (![A_167, B_168, C_169]: (r2_hidden(A_167, B_168) | ~r2_hidden(A_167, k1_relat_1(k7_relat_1(C_169, B_168))) | ~v1_relat_1(C_169))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.19/1.89  tff(c_787, plain, (![A_167]: (r2_hidden(A_167, '#skF_3') | ~r2_hidden(A_167, k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_660, c_784])).
% 4.19/1.89  tff(c_822, plain, (![A_171]: (r2_hidden(A_171, '#skF_3') | ~r2_hidden(A_171, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_586, c_787])).
% 4.19/1.89  tff(c_827, plain, (r2_hidden('#skF_1'(k1_relat_1('#skF_4')), '#skF_3') | v1_xboole_0(k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_4, c_822])).
% 4.19/1.89  tff(c_930, plain, (v1_xboole_0(k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_827])).
% 4.19/1.89  tff(c_941, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_930, c_6])).
% 4.19/1.89  tff(c_1400, plain, (![D_215, B_216, C_217, A_218]: (m1_subset_1(D_215, k1_zfmisc_1(k2_zfmisc_1(B_216, C_217))) | ~r1_tarski(k1_relat_1(D_215), B_216) | ~m1_subset_1(D_215, k1_zfmisc_1(k2_zfmisc_1(A_218, C_217))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.19/1.89  tff(c_1412, plain, (![B_216]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_216, '#skF_2'))) | ~r1_tarski(k1_relat_1('#skF_4'), B_216))), inference(resolution, [status(thm)], [c_46, c_1400])).
% 4.19/1.89  tff(c_1453, plain, (![B_219]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_219, '#skF_2'))) | ~r1_tarski(k1_xboole_0, B_219))), inference(demodulation, [status(thm), theory('equality')], [c_941, c_1412])).
% 4.19/1.89  tff(c_1484, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_740, c_1453])).
% 4.19/1.89  tff(c_1498, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_1484])).
% 4.19/1.89  tff(c_742, plain, (![B_165]: (k2_zfmisc_1(k1_xboole_0, B_165)=k1_xboole_0)), inference(resolution, [status(thm)], [c_538, c_732])).
% 4.19/1.89  tff(c_34, plain, (![C_27, A_24, B_25]: (v1_xboole_0(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))) | ~v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.19/1.89  tff(c_750, plain, (![C_27]: (v1_xboole_0(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_742, c_34])).
% 4.19/1.89  tff(c_781, plain, (![C_27]: (v1_xboole_0(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_538, c_750])).
% 4.19/1.89  tff(c_1515, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1498, c_781])).
% 4.19/1.89  tff(c_68, plain, (![A_55]: (k2_relat_1(A_55)=k1_xboole_0 | ~v1_xboole_0(A_55))), inference(resolution, [status(thm)], [c_64, c_6])).
% 4.19/1.89  tff(c_1523, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_1515, c_68])).
% 4.19/1.89  tff(c_1531, plain, $false, inference(negUnitSimplification, [status(thm)], [c_903, c_1523])).
% 4.19/1.89  tff(c_1532, plain, (r2_hidden('#skF_1'(k1_relat_1('#skF_4')), '#skF_3')), inference(splitRight, [status(thm)], [c_827])).
% 4.19/1.89  tff(c_1540, plain, (m1_subset_1('#skF_1'(k1_relat_1('#skF_4')), '#skF_3')), inference(resolution, [status(thm)], [c_1532, c_12])).
% 4.19/1.89  tff(c_1542, plain, (![A_220, B_221, C_222]: (k1_relset_1(A_220, B_221, C_222)=k1_relat_1(C_222) | ~m1_subset_1(C_222, k1_zfmisc_1(k2_zfmisc_1(A_220, B_221))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.19/1.89  tff(c_1563, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_1542])).
% 4.19/1.89  tff(c_562, plain, (![D_130]: (~r2_hidden(D_130, k1_relset_1('#skF_3', '#skF_2', '#skF_4')) | ~m1_subset_1(D_130, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.19/1.89  tff(c_567, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_3', '#skF_2', '#skF_4')), '#skF_3') | v1_xboole_0(k1_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_4, c_562])).
% 4.19/1.89  tff(c_645, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_3', '#skF_2', '#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_567])).
% 4.19/1.89  tff(c_1565, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1563, c_645])).
% 4.19/1.89  tff(c_1569, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1540, c_1565])).
% 4.19/1.89  tff(c_1570, plain, (v1_xboole_0(k1_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_567])).
% 4.19/1.89  tff(c_1579, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_1570, c_6])).
% 4.19/1.89  tff(c_1831, plain, (![A_251, B_252, C_253]: (k1_relset_1(A_251, B_252, C_253)=k1_relat_1(C_253) | ~m1_subset_1(C_253, k1_zfmisc_1(k2_zfmisc_1(A_251, B_252))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.19/1.89  tff(c_1845, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_1831])).
% 4.19/1.89  tff(c_1853, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1579, c_1845])).
% 4.19/1.89  tff(c_2471, plain, (![D_301, B_302, C_303, A_304]: (m1_subset_1(D_301, k1_zfmisc_1(k2_zfmisc_1(B_302, C_303))) | ~r1_tarski(k1_relat_1(D_301), B_302) | ~m1_subset_1(D_301, k1_zfmisc_1(k2_zfmisc_1(A_304, C_303))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.19/1.89  tff(c_2483, plain, (![B_302]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_302, '#skF_2'))) | ~r1_tarski(k1_relat_1('#skF_4'), B_302))), inference(resolution, [status(thm)], [c_46, c_2471])).
% 4.19/1.89  tff(c_2617, plain, (![B_312]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_312, '#skF_2'))) | ~r1_tarski(k1_xboole_0, B_312))), inference(demodulation, [status(thm), theory('equality')], [c_1853, c_2483])).
% 4.19/1.89  tff(c_2652, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1673, c_2617])).
% 4.19/1.89  tff(c_2666, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_2652])).
% 4.19/1.89  tff(c_1675, plain, (![B_238]: (k2_zfmisc_1(k1_xboole_0, B_238)=k1_xboole_0)), inference(resolution, [status(thm)], [c_538, c_1665])).
% 4.19/1.89  tff(c_1683, plain, (![C_27]: (v1_xboole_0(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1675, c_34])).
% 4.19/1.89  tff(c_1711, plain, (![C_27]: (v1_xboole_0(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_538, c_1683])).
% 4.19/1.89  tff(c_2683, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_2666, c_1711])).
% 4.19/1.89  tff(c_2691, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_2683, c_68])).
% 4.19/1.89  tff(c_2699, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2032, c_2691])).
% 4.19/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.19/1.89  
% 4.19/1.89  Inference rules
% 4.19/1.89  ----------------------
% 4.19/1.89  #Ref     : 0
% 4.19/1.89  #Sup     : 574
% 4.19/1.89  #Fact    : 0
% 4.19/1.89  #Define  : 0
% 4.19/1.89  #Split   : 5
% 4.19/1.89  #Chain   : 0
% 4.19/1.89  #Close   : 0
% 4.19/1.89  
% 4.19/1.89  Ordering : KBO
% 4.19/1.89  
% 4.19/1.89  Simplification rules
% 4.19/1.89  ----------------------
% 4.19/1.89  #Subsume      : 50
% 4.19/1.89  #Demod        : 313
% 4.19/1.89  #Tautology    : 242
% 4.19/1.89  #SimpNegUnit  : 20
% 4.19/1.89  #BackRed      : 31
% 4.19/1.89  
% 4.19/1.89  #Partial instantiations: 0
% 4.19/1.89  #Strategies tried      : 1
% 4.19/1.89  
% 4.19/1.89  Timing (in seconds)
% 4.19/1.89  ----------------------
% 4.19/1.89  Preprocessing        : 0.35
% 4.19/1.89  Parsing              : 0.19
% 4.19/1.89  CNF conversion       : 0.03
% 4.19/1.89  Main loop            : 0.67
% 4.19/1.89  Inferencing          : 0.25
% 4.19/1.89  Reduction            : 0.22
% 4.19/1.89  Demodulation         : 0.15
% 4.19/1.89  BG Simplification    : 0.03
% 4.19/1.89  Subsumption          : 0.12
% 4.19/1.89  Abstraction          : 0.03
% 4.19/1.89  MUC search           : 0.00
% 4.19/1.89  Cooper               : 0.00
% 4.19/1.89  Total                : 1.09
% 4.19/1.89  Index Insertion      : 0.00
% 4.19/1.89  Index Deletion       : 0.00
% 4.19/1.89  Index Matching       : 0.00
% 4.19/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
