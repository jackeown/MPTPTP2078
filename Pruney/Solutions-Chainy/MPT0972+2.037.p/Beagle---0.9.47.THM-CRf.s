%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:40 EST 2020

% Result     : Theorem 14.40s
% Output     : CNFRefutation 14.40s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 613 expanded)
%              Number of leaves         :   39 ( 230 expanded)
%              Depth                    :   14
%              Number of atoms          :  335 (2384 expanded)
%              Number of equality atoms :   66 ( 439 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_8 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_157,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ! [E] :
                  ( r2_hidden(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

tff(f_118,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_136,axiom,(
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

tff(f_80,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k1_relat_1(A) = k1_relat_1(B)
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ! [D] :
          ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( r2_relset_1(A,B,C,D)
          <=> ! [E] :
                ( m1_subset_1(E,A)
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ( r2_hidden(k4_tarski(E,F),C)
                    <=> r2_hidden(k4_tarski(E,F),D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relset_1)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_43,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_74,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_35043,plain,(
    ! [A_833,B_834,D_835] :
      ( r2_relset_1(A_833,B_834,D_835,D_835)
      | ~ m1_subset_1(D_835,k1_zfmisc_1(k2_zfmisc_1(A_833,B_834))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_35056,plain,(
    r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_74,c_35043])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_180,plain,(
    ! [A_87,B_88] :
      ( ~ r2_hidden('#skF_1'(A_87,B_88),B_88)
      | r1_tarski(A_87,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_185,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_180])).

tff(c_80,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_186,plain,(
    ! [C_89,A_90,B_91] :
      ( v1_relat_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_206,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_80,c_186])).

tff(c_84,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_82,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_1119,plain,(
    ! [A_162,B_163,C_164] :
      ( k1_relset_1(A_162,B_163,C_164) = k1_relat_1(C_164)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1141,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_80,c_1119])).

tff(c_2227,plain,(
    ! [B_207,A_208,C_209] :
      ( k1_xboole_0 = B_207
      | k1_relset_1(A_208,B_207,C_209) = A_208
      | ~ v1_funct_2(C_209,A_208,B_207)
      | ~ m1_subset_1(C_209,k1_zfmisc_1(k2_zfmisc_1(A_208,B_207))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_2234,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_2227])).

tff(c_2251,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1141,c_2234])).

tff(c_2257,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_2251])).

tff(c_207,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_74,c_186])).

tff(c_78,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_76,plain,(
    v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_1142,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_74,c_1119])).

tff(c_2237,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_2227])).

tff(c_2254,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1142,c_2237])).

tff(c_2263,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_2254])).

tff(c_2987,plain,(
    ! [A_221,B_222] :
      ( r2_hidden('#skF_2'(A_221,B_222),k1_relat_1(A_221))
      | B_222 = A_221
      | k1_relat_1(B_222) != k1_relat_1(A_221)
      | ~ v1_funct_1(B_222)
      | ~ v1_relat_1(B_222)
      | ~ v1_funct_1(A_221)
      | ~ v1_relat_1(A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2997,plain,(
    ! [B_222] :
      ( r2_hidden('#skF_2'('#skF_8',B_222),'#skF_5')
      | B_222 = '#skF_8'
      | k1_relat_1(B_222) != k1_relat_1('#skF_8')
      | ~ v1_funct_1(B_222)
      | ~ v1_relat_1(B_222)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2263,c_2987])).

tff(c_33795,plain,(
    ! [B_802] :
      ( r2_hidden('#skF_2'('#skF_8',B_802),'#skF_5')
      | B_802 = '#skF_8'
      | k1_relat_1(B_802) != '#skF_5'
      | ~ v1_funct_1(B_802)
      | ~ v1_relat_1(B_802) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_78,c_2263,c_2997])).

tff(c_72,plain,(
    ! [E_70] :
      ( k1_funct_1('#skF_7',E_70) = k1_funct_1('#skF_8',E_70)
      | ~ r2_hidden(E_70,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_33977,plain,(
    ! [B_804] :
      ( k1_funct_1('#skF_7','#skF_2'('#skF_8',B_804)) = k1_funct_1('#skF_8','#skF_2'('#skF_8',B_804))
      | B_804 = '#skF_8'
      | k1_relat_1(B_804) != '#skF_5'
      | ~ v1_funct_1(B_804)
      | ~ v1_relat_1(B_804) ) ),
    inference(resolution,[status(thm)],[c_33795,c_72])).

tff(c_28,plain,(
    ! [B_22,A_18] :
      ( k1_funct_1(B_22,'#skF_2'(A_18,B_22)) != k1_funct_1(A_18,'#skF_2'(A_18,B_22))
      | B_22 = A_18
      | k1_relat_1(B_22) != k1_relat_1(A_18)
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_33984,plain,
    ( k1_relat_1('#skF_7') != k1_relat_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | '#skF_7' = '#skF_8'
    | k1_relat_1('#skF_7') != '#skF_5'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_33977,c_28])).

tff(c_33991,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_84,c_2257,c_207,c_78,c_2257,c_2263,c_33984])).

tff(c_70,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_5167,plain,(
    ! [A_297,B_298,C_299,D_300] :
      ( r2_hidden(k4_tarski('#skF_3'(A_297,B_298,C_299,D_300),'#skF_4'(A_297,B_298,C_299,D_300)),C_299)
      | r2_hidden(k4_tarski('#skF_3'(A_297,B_298,C_299,D_300),'#skF_4'(A_297,B_298,C_299,D_300)),D_300)
      | r2_relset_1(A_297,B_298,C_299,D_300)
      | ~ m1_subset_1(D_300,k1_zfmisc_1(k2_zfmisc_1(A_297,B_298)))
      | ~ m1_subset_1(C_299,k1_zfmisc_1(k2_zfmisc_1(A_297,B_298))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5227,plain,(
    ! [C_299,B_2,D_300,B_298,A_297] :
      ( r2_hidden(k4_tarski('#skF_3'(A_297,B_298,C_299,D_300),'#skF_4'(A_297,B_298,C_299,D_300)),B_2)
      | ~ r1_tarski(D_300,B_2)
      | r2_hidden(k4_tarski('#skF_3'(A_297,B_298,C_299,D_300),'#skF_4'(A_297,B_298,C_299,D_300)),C_299)
      | r2_relset_1(A_297,B_298,C_299,D_300)
      | ~ m1_subset_1(D_300,k1_zfmisc_1(k2_zfmisc_1(A_297,B_298)))
      | ~ m1_subset_1(C_299,k1_zfmisc_1(k2_zfmisc_1(A_297,B_298))) ) ),
    inference(resolution,[status(thm)],[c_5167,c_2])).

tff(c_27020,plain,(
    ! [B_682] :
      ( r2_hidden('#skF_2'('#skF_8',B_682),'#skF_5')
      | B_682 = '#skF_8'
      | k1_relat_1(B_682) != '#skF_5'
      | ~ v1_funct_1(B_682)
      | ~ v1_relat_1(B_682) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_78,c_2263,c_2997])).

tff(c_27040,plain,(
    ! [B_685] :
      ( k1_funct_1('#skF_7','#skF_2'('#skF_8',B_685)) = k1_funct_1('#skF_8','#skF_2'('#skF_8',B_685))
      | B_685 = '#skF_8'
      | k1_relat_1(B_685) != '#skF_5'
      | ~ v1_funct_1(B_685)
      | ~ v1_relat_1(B_685) ) ),
    inference(resolution,[status(thm)],[c_27020,c_72])).

tff(c_27047,plain,
    ( k1_relat_1('#skF_7') != k1_relat_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | '#skF_7' = '#skF_8'
    | k1_relat_1('#skF_7') != '#skF_5'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_27040,c_28])).

tff(c_27054,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_84,c_2257,c_207,c_78,c_2257,c_2263,c_27047])).

tff(c_5219,plain,(
    ! [C_299,B_2,D_300,B_298,A_297] :
      ( r2_hidden(k4_tarski('#skF_3'(A_297,B_298,C_299,D_300),'#skF_4'(A_297,B_298,C_299,D_300)),B_2)
      | ~ r1_tarski(C_299,B_2)
      | r2_hidden(k4_tarski('#skF_3'(A_297,B_298,C_299,D_300),'#skF_4'(A_297,B_298,C_299,D_300)),D_300)
      | r2_relset_1(A_297,B_298,C_299,D_300)
      | ~ m1_subset_1(D_300,k1_zfmisc_1(k2_zfmisc_1(A_297,B_298)))
      | ~ m1_subset_1(C_299,k1_zfmisc_1(k2_zfmisc_1(A_297,B_298))) ) ),
    inference(resolution,[status(thm)],[c_5167,c_2])).

tff(c_3253,plain,(
    ! [A_238,B_239,C_240,D_241] :
      ( m1_subset_1('#skF_4'(A_238,B_239,C_240,D_241),B_239)
      | r2_relset_1(A_238,B_239,C_240,D_241)
      | ~ m1_subset_1(D_241,k1_zfmisc_1(k2_zfmisc_1(A_238,B_239)))
      | ~ m1_subset_1(C_240,k1_zfmisc_1(k2_zfmisc_1(A_238,B_239))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_3305,plain,(
    ! [C_246] :
      ( m1_subset_1('#skF_4'('#skF_5','#skF_6',C_246,'#skF_8'),'#skF_6')
      | r2_relset_1('#skF_5','#skF_6',C_246,'#skF_8')
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_74,c_3253])).

tff(c_3312,plain,
    ( m1_subset_1('#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6')
    | r2_relset_1('#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_80,c_3305])).

tff(c_3323,plain,(
    m1_subset_1('#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_3312])).

tff(c_50,plain,(
    ! [A_29,D_45,E_52,F_54,C_31,B_30] :
      ( r2_hidden(k4_tarski(E_52,F_54),D_45)
      | ~ r2_hidden(k4_tarski(E_52,F_54),C_31)
      | ~ m1_subset_1(F_54,B_30)
      | ~ m1_subset_1(E_52,A_29)
      | ~ r2_relset_1(A_29,B_30,C_31,D_45)
      | ~ m1_subset_1(D_45,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30)))
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_19963,plain,(
    ! [D_571,A_569,C_567,D_565,A_568,B_570,B_566] :
      ( r2_hidden(k4_tarski('#skF_3'(A_569,B_570,C_567,D_571),'#skF_4'(A_569,B_570,C_567,D_571)),D_565)
      | ~ m1_subset_1('#skF_4'(A_569,B_570,C_567,D_571),B_566)
      | ~ m1_subset_1('#skF_3'(A_569,B_570,C_567,D_571),A_568)
      | ~ r2_relset_1(A_568,B_566,D_571,D_565)
      | ~ m1_subset_1(D_565,k1_zfmisc_1(k2_zfmisc_1(A_568,B_566)))
      | ~ m1_subset_1(D_571,k1_zfmisc_1(k2_zfmisc_1(A_568,B_566)))
      | r2_hidden(k4_tarski('#skF_3'(A_569,B_570,C_567,D_571),'#skF_4'(A_569,B_570,C_567,D_571)),C_567)
      | r2_relset_1(A_569,B_570,C_567,D_571)
      | ~ m1_subset_1(D_571,k1_zfmisc_1(k2_zfmisc_1(A_569,B_570)))
      | ~ m1_subset_1(C_567,k1_zfmisc_1(k2_zfmisc_1(A_569,B_570))) ) ),
    inference(resolution,[status(thm)],[c_5167,c_50])).

tff(c_19991,plain,(
    ! [D_565,A_568] :
      ( r2_hidden(k4_tarski('#skF_3'('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8')),D_565)
      | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6','#skF_7','#skF_8'),A_568)
      | ~ r2_relset_1(A_568,'#skF_6','#skF_8',D_565)
      | ~ m1_subset_1(D_565,k1_zfmisc_1(k2_zfmisc_1(A_568,'#skF_6')))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(A_568,'#skF_6')))
      | r2_hidden(k4_tarski('#skF_3'('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8')),'#skF_7')
      | r2_relset_1('#skF_5','#skF_6','#skF_7','#skF_8')
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_3323,c_19963])).

tff(c_20039,plain,(
    ! [D_565,A_568] :
      ( r2_hidden(k4_tarski('#skF_3'('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8')),D_565)
      | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6','#skF_7','#skF_8'),A_568)
      | ~ r2_relset_1(A_568,'#skF_6','#skF_8',D_565)
      | ~ m1_subset_1(D_565,k1_zfmisc_1(k2_zfmisc_1(A_568,'#skF_6')))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(A_568,'#skF_6')))
      | r2_hidden(k4_tarski('#skF_3'('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8')),'#skF_7')
      | r2_relset_1('#skF_5','#skF_6','#skF_7','#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_74,c_19991])).

tff(c_20040,plain,(
    ! [D_565,A_568] :
      ( r2_hidden(k4_tarski('#skF_3'('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8')),D_565)
      | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6','#skF_7','#skF_8'),A_568)
      | ~ r2_relset_1(A_568,'#skF_6','#skF_8',D_565)
      | ~ m1_subset_1(D_565,k1_zfmisc_1(k2_zfmisc_1(A_568,'#skF_6')))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(A_568,'#skF_6')))
      | r2_hidden(k4_tarski('#skF_3'('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8')),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_20039])).

tff(c_20475,plain,(
    r2_hidden(k4_tarski('#skF_3'('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8')),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_20040])).

tff(c_48,plain,(
    ! [A_29,D_45,E_52,F_54,C_31,B_30] :
      ( r2_hidden(k4_tarski(E_52,F_54),C_31)
      | ~ r2_hidden(k4_tarski(E_52,F_54),D_45)
      | ~ m1_subset_1(F_54,B_30)
      | ~ m1_subset_1(E_52,A_29)
      | ~ r2_relset_1(A_29,B_30,C_31,D_45)
      | ~ m1_subset_1(D_45,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30)))
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_21642,plain,(
    ! [B_606,A_605,C_603,D_608,C_607,A_604,B_602] :
      ( r2_hidden(k4_tarski('#skF_3'(A_605,B_606,C_603,D_608),'#skF_4'(A_605,B_606,C_603,D_608)),C_607)
      | ~ m1_subset_1('#skF_4'(A_605,B_606,C_603,D_608),B_602)
      | ~ m1_subset_1('#skF_3'(A_605,B_606,C_603,D_608),A_604)
      | ~ r2_relset_1(A_604,B_602,C_607,C_603)
      | ~ m1_subset_1(C_603,k1_zfmisc_1(k2_zfmisc_1(A_604,B_602)))
      | ~ m1_subset_1(C_607,k1_zfmisc_1(k2_zfmisc_1(A_604,B_602)))
      | r2_hidden(k4_tarski('#skF_3'(A_605,B_606,C_603,D_608),'#skF_4'(A_605,B_606,C_603,D_608)),D_608)
      | r2_relset_1(A_605,B_606,C_603,D_608)
      | ~ m1_subset_1(D_608,k1_zfmisc_1(k2_zfmisc_1(A_605,B_606)))
      | ~ m1_subset_1(C_603,k1_zfmisc_1(k2_zfmisc_1(A_605,B_606))) ) ),
    inference(resolution,[status(thm)],[c_5167,c_48])).

tff(c_21670,plain,(
    ! [C_607,A_604] :
      ( r2_hidden(k4_tarski('#skF_3'('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8')),C_607)
      | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6','#skF_7','#skF_8'),A_604)
      | ~ r2_relset_1(A_604,'#skF_6',C_607,'#skF_7')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_604,'#skF_6')))
      | ~ m1_subset_1(C_607,k1_zfmisc_1(k2_zfmisc_1(A_604,'#skF_6')))
      | r2_hidden(k4_tarski('#skF_3'('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8')),'#skF_8')
      | r2_relset_1('#skF_5','#skF_6','#skF_7','#skF_8')
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_3323,c_21642])).

tff(c_21718,plain,(
    ! [C_607,A_604] :
      ( r2_hidden(k4_tarski('#skF_3'('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8')),C_607)
      | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6','#skF_7','#skF_8'),A_604)
      | ~ r2_relset_1(A_604,'#skF_6',C_607,'#skF_7')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_604,'#skF_6')))
      | ~ m1_subset_1(C_607,k1_zfmisc_1(k2_zfmisc_1(A_604,'#skF_6')))
      | r2_hidden(k4_tarski('#skF_3'('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8')),'#skF_8')
      | r2_relset_1('#skF_5','#skF_6','#skF_7','#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_74,c_21670])).

tff(c_21719,plain,(
    ! [C_607,A_604] :
      ( r2_hidden(k4_tarski('#skF_3'('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8')),C_607)
      | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6','#skF_7','#skF_8'),A_604)
      | ~ r2_relset_1(A_604,'#skF_6',C_607,'#skF_7')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_604,'#skF_6')))
      | ~ m1_subset_1(C_607,k1_zfmisc_1(k2_zfmisc_1(A_604,'#skF_6')))
      | r2_hidden(k4_tarski('#skF_3'('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8')),'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_21718])).

tff(c_24872,plain,(
    r2_hidden(k4_tarski('#skF_3'('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8')),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_21719])).

tff(c_40,plain,(
    ! [A_29,B_30,C_31,D_45] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(A_29,B_30,C_31,D_45),'#skF_4'(A_29,B_30,C_31,D_45)),D_45)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_29,B_30,C_31,D_45),'#skF_4'(A_29,B_30,C_31,D_45)),C_31)
      | r2_relset_1(A_29,B_30,C_31,D_45)
      | ~ m1_subset_1(D_45,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30)))
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_24874,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3'('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8')),'#skF_7')
    | r2_relset_1('#skF_5','#skF_6','#skF_7','#skF_8')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_24872,c_40])).

tff(c_24888,plain,(
    r2_relset_1('#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_74,c_20475,c_24874])).

tff(c_24890,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_24888])).

tff(c_24892,plain,(
    ~ r2_hidden(k4_tarski('#skF_3'('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8')),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_21719])).

tff(c_24899,plain,(
    ! [B_2] :
      ( r2_hidden(k4_tarski('#skF_3'('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8')),B_2)
      | ~ r1_tarski('#skF_7',B_2)
      | r2_relset_1('#skF_5','#skF_6','#skF_7','#skF_8')
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_5219,c_24892])).

tff(c_24908,plain,(
    ! [B_2] :
      ( r2_hidden(k4_tarski('#skF_3'('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8')),B_2)
      | ~ r1_tarski('#skF_7',B_2)
      | r2_relset_1('#skF_5','#skF_6','#skF_7','#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_74,c_24899])).

tff(c_25297,plain,(
    ! [B_648] :
      ( r2_hidden(k4_tarski('#skF_3'('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8')),B_648)
      | ~ r1_tarski('#skF_7',B_648) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_24908])).

tff(c_25327,plain,(
    ~ r1_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_25297,c_24892])).

tff(c_27072,plain,(
    ~ r1_tarski('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27054,c_25327])).

tff(c_27162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_27072])).

tff(c_27164,plain,(
    ~ r2_hidden(k4_tarski('#skF_3'('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8')),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_20040])).

tff(c_27287,plain,(
    ! [B_2] :
      ( r2_hidden(k4_tarski('#skF_3'('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8')),B_2)
      | ~ r1_tarski('#skF_8',B_2)
      | r2_relset_1('#skF_5','#skF_6','#skF_7','#skF_8')
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_5227,c_27164])).

tff(c_27301,plain,(
    ! [B_2] :
      ( r2_hidden(k4_tarski('#skF_3'('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8')),B_2)
      | ~ r1_tarski('#skF_8',B_2)
      | r2_relset_1('#skF_5','#skF_6','#skF_7','#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_74,c_27287])).

tff(c_27709,plain,(
    ! [B_697] :
      ( r2_hidden(k4_tarski('#skF_3'('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8')),B_697)
      | ~ r1_tarski('#skF_8',B_697) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_27301])).

tff(c_27739,plain,(
    ~ r1_tarski('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_27709,c_27164])).

tff(c_34008,plain,(
    ~ r1_tarski('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33991,c_27739])).

tff(c_34089,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_34008])).

tff(c_34090,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2254])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_34123,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34090,c_8])).

tff(c_16,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_34121,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34090,c_34090,c_16])).

tff(c_463,plain,(
    ! [C_121,B_122,A_123] :
      ( ~ v1_xboole_0(C_121)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(C_121))
      | ~ r2_hidden(A_123,B_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_478,plain,(
    ! [A_123] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6'))
      | ~ r2_hidden(A_123,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_80,c_463])).

tff(c_538,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_478])).

tff(c_34385,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34121,c_538])).

tff(c_34394,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34123,c_34385])).

tff(c_34395,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2251])).

tff(c_34429,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34395,c_8])).

tff(c_34427,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34395,c_34395,c_16])).

tff(c_34696,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34427,c_538])).

tff(c_34705,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34429,c_34696])).

tff(c_34707,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_478])).

tff(c_479,plain,(
    ! [A_123] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6'))
      | ~ r2_hidden(A_123,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_74,c_463])).

tff(c_34708,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_479])).

tff(c_34809,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34707,c_34708])).

tff(c_34818,plain,(
    ! [A_826] : ~ r2_hidden(A_826,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_479])).

tff(c_34823,plain,(
    ! [B_2] : r1_tarski('#skF_8',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_34818])).

tff(c_34812,plain,(
    ! [A_825] : ~ r2_hidden(A_825,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_478])).

tff(c_34825,plain,(
    ! [B_827] : r1_tarski('#skF_7',B_827) ),
    inference(resolution,[status(thm)],[c_6,c_34812])).

tff(c_12,plain,(
    ! [A_9] :
      ( k1_xboole_0 = A_9
      | ~ r1_tarski(A_9,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_34863,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_34825,c_12])).

tff(c_35128,plain,(
    ! [A_838] :
      ( A_838 = '#skF_7'
      | ~ r1_tarski(A_838,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34863,c_34863,c_12])).

tff(c_35153,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_34823,c_35128])).

tff(c_35180,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35153,c_70])).

tff(c_35189,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_35056,c_35180])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:59:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.40/6.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.40/6.55  
% 14.40/6.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.40/6.55  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_8 > #skF_2 > #skF_3 > #skF_1
% 14.40/6.55  
% 14.40/6.55  %Foreground sorts:
% 14.40/6.55  
% 14.40/6.55  
% 14.40/6.55  %Background operators:
% 14.40/6.55  
% 14.40/6.55  
% 14.40/6.55  %Foreground operators:
% 14.40/6.55  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 14.40/6.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.40/6.55  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 14.40/6.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.40/6.55  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 14.40/6.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.40/6.55  tff('#skF_7', type, '#skF_7': $i).
% 14.40/6.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.40/6.55  tff('#skF_5', type, '#skF_5': $i).
% 14.40/6.55  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 14.40/6.55  tff('#skF_6', type, '#skF_6': $i).
% 14.40/6.55  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 14.40/6.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.40/6.55  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 14.40/6.55  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 14.40/6.55  tff('#skF_8', type, '#skF_8': $i).
% 14.40/6.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.40/6.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.40/6.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 14.40/6.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.40/6.55  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 14.40/6.55  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 14.40/6.55  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 14.40/6.55  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 14.40/6.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 14.40/6.55  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 14.40/6.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.40/6.55  
% 14.40/6.57  tff(f_157, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_2)).
% 14.40/6.57  tff(f_118, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 14.40/6.57  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 14.40/6.57  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 14.40/6.57  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 14.40/6.57  tff(f_136, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 14.40/6.57  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 14.40/6.57  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, C, D) <=> (![E]: (m1_subset_1(E, A) => (![F]: (m1_subset_1(F, B) => (r2_hidden(k4_tarski(E, F), C) <=> r2_hidden(k4_tarski(E, F), D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relset_1)).
% 14.40/6.57  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 14.40/6.57  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 14.40/6.57  tff(f_62, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 14.40/6.57  tff(f_43, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 14.40/6.57  tff(c_74, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_157])).
% 14.40/6.57  tff(c_35043, plain, (![A_833, B_834, D_835]: (r2_relset_1(A_833, B_834, D_835, D_835) | ~m1_subset_1(D_835, k1_zfmisc_1(k2_zfmisc_1(A_833, B_834))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 14.40/6.57  tff(c_35056, plain, (r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_74, c_35043])).
% 14.40/6.57  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.40/6.57  tff(c_180, plain, (![A_87, B_88]: (~r2_hidden('#skF_1'(A_87, B_88), B_88) | r1_tarski(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.40/6.57  tff(c_185, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_180])).
% 14.40/6.57  tff(c_80, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_157])).
% 14.40/6.57  tff(c_186, plain, (![C_89, A_90, B_91]: (v1_relat_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 14.40/6.57  tff(c_206, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_80, c_186])).
% 14.40/6.57  tff(c_84, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_157])).
% 14.40/6.57  tff(c_82, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_157])).
% 14.40/6.57  tff(c_1119, plain, (![A_162, B_163, C_164]: (k1_relset_1(A_162, B_163, C_164)=k1_relat_1(C_164) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 14.40/6.57  tff(c_1141, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_80, c_1119])).
% 14.40/6.57  tff(c_2227, plain, (![B_207, A_208, C_209]: (k1_xboole_0=B_207 | k1_relset_1(A_208, B_207, C_209)=A_208 | ~v1_funct_2(C_209, A_208, B_207) | ~m1_subset_1(C_209, k1_zfmisc_1(k2_zfmisc_1(A_208, B_207))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 14.40/6.57  tff(c_2234, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_5' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_80, c_2227])).
% 14.40/6.57  tff(c_2251, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1141, c_2234])).
% 14.40/6.57  tff(c_2257, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitLeft, [status(thm)], [c_2251])).
% 14.40/6.57  tff(c_207, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_74, c_186])).
% 14.40/6.57  tff(c_78, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_157])).
% 14.40/6.57  tff(c_76, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_157])).
% 14.40/6.57  tff(c_1142, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_74, c_1119])).
% 14.40/6.57  tff(c_2237, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_74, c_2227])).
% 14.40/6.57  tff(c_2254, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1142, c_2237])).
% 14.40/6.57  tff(c_2263, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_2254])).
% 14.40/6.57  tff(c_2987, plain, (![A_221, B_222]: (r2_hidden('#skF_2'(A_221, B_222), k1_relat_1(A_221)) | B_222=A_221 | k1_relat_1(B_222)!=k1_relat_1(A_221) | ~v1_funct_1(B_222) | ~v1_relat_1(B_222) | ~v1_funct_1(A_221) | ~v1_relat_1(A_221))), inference(cnfTransformation, [status(thm)], [f_80])).
% 14.40/6.57  tff(c_2997, plain, (![B_222]: (r2_hidden('#skF_2'('#skF_8', B_222), '#skF_5') | B_222='#skF_8' | k1_relat_1(B_222)!=k1_relat_1('#skF_8') | ~v1_funct_1(B_222) | ~v1_relat_1(B_222) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_2263, c_2987])).
% 14.40/6.57  tff(c_33795, plain, (![B_802]: (r2_hidden('#skF_2'('#skF_8', B_802), '#skF_5') | B_802='#skF_8' | k1_relat_1(B_802)!='#skF_5' | ~v1_funct_1(B_802) | ~v1_relat_1(B_802))), inference(demodulation, [status(thm), theory('equality')], [c_207, c_78, c_2263, c_2997])).
% 14.40/6.57  tff(c_72, plain, (![E_70]: (k1_funct_1('#skF_7', E_70)=k1_funct_1('#skF_8', E_70) | ~r2_hidden(E_70, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 14.40/6.57  tff(c_33977, plain, (![B_804]: (k1_funct_1('#skF_7', '#skF_2'('#skF_8', B_804))=k1_funct_1('#skF_8', '#skF_2'('#skF_8', B_804)) | B_804='#skF_8' | k1_relat_1(B_804)!='#skF_5' | ~v1_funct_1(B_804) | ~v1_relat_1(B_804))), inference(resolution, [status(thm)], [c_33795, c_72])).
% 14.40/6.57  tff(c_28, plain, (![B_22, A_18]: (k1_funct_1(B_22, '#skF_2'(A_18, B_22))!=k1_funct_1(A_18, '#skF_2'(A_18, B_22)) | B_22=A_18 | k1_relat_1(B_22)!=k1_relat_1(A_18) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_80])).
% 14.40/6.57  tff(c_33984, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | '#skF_7'='#skF_8' | k1_relat_1('#skF_7')!='#skF_5' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_33977, c_28])).
% 14.40/6.57  tff(c_33991, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_206, c_84, c_2257, c_207, c_78, c_2257, c_2263, c_33984])).
% 14.40/6.57  tff(c_70, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_157])).
% 14.40/6.57  tff(c_5167, plain, (![A_297, B_298, C_299, D_300]: (r2_hidden(k4_tarski('#skF_3'(A_297, B_298, C_299, D_300), '#skF_4'(A_297, B_298, C_299, D_300)), C_299) | r2_hidden(k4_tarski('#skF_3'(A_297, B_298, C_299, D_300), '#skF_4'(A_297, B_298, C_299, D_300)), D_300) | r2_relset_1(A_297, B_298, C_299, D_300) | ~m1_subset_1(D_300, k1_zfmisc_1(k2_zfmisc_1(A_297, B_298))) | ~m1_subset_1(C_299, k1_zfmisc_1(k2_zfmisc_1(A_297, B_298))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.40/6.57  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.40/6.57  tff(c_5227, plain, (![C_299, B_2, D_300, B_298, A_297]: (r2_hidden(k4_tarski('#skF_3'(A_297, B_298, C_299, D_300), '#skF_4'(A_297, B_298, C_299, D_300)), B_2) | ~r1_tarski(D_300, B_2) | r2_hidden(k4_tarski('#skF_3'(A_297, B_298, C_299, D_300), '#skF_4'(A_297, B_298, C_299, D_300)), C_299) | r2_relset_1(A_297, B_298, C_299, D_300) | ~m1_subset_1(D_300, k1_zfmisc_1(k2_zfmisc_1(A_297, B_298))) | ~m1_subset_1(C_299, k1_zfmisc_1(k2_zfmisc_1(A_297, B_298))))), inference(resolution, [status(thm)], [c_5167, c_2])).
% 14.40/6.57  tff(c_27020, plain, (![B_682]: (r2_hidden('#skF_2'('#skF_8', B_682), '#skF_5') | B_682='#skF_8' | k1_relat_1(B_682)!='#skF_5' | ~v1_funct_1(B_682) | ~v1_relat_1(B_682))), inference(demodulation, [status(thm), theory('equality')], [c_207, c_78, c_2263, c_2997])).
% 14.40/6.57  tff(c_27040, plain, (![B_685]: (k1_funct_1('#skF_7', '#skF_2'('#skF_8', B_685))=k1_funct_1('#skF_8', '#skF_2'('#skF_8', B_685)) | B_685='#skF_8' | k1_relat_1(B_685)!='#skF_5' | ~v1_funct_1(B_685) | ~v1_relat_1(B_685))), inference(resolution, [status(thm)], [c_27020, c_72])).
% 14.40/6.57  tff(c_27047, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | '#skF_7'='#skF_8' | k1_relat_1('#skF_7')!='#skF_5' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_27040, c_28])).
% 14.40/6.57  tff(c_27054, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_206, c_84, c_2257, c_207, c_78, c_2257, c_2263, c_27047])).
% 14.40/6.57  tff(c_5219, plain, (![C_299, B_2, D_300, B_298, A_297]: (r2_hidden(k4_tarski('#skF_3'(A_297, B_298, C_299, D_300), '#skF_4'(A_297, B_298, C_299, D_300)), B_2) | ~r1_tarski(C_299, B_2) | r2_hidden(k4_tarski('#skF_3'(A_297, B_298, C_299, D_300), '#skF_4'(A_297, B_298, C_299, D_300)), D_300) | r2_relset_1(A_297, B_298, C_299, D_300) | ~m1_subset_1(D_300, k1_zfmisc_1(k2_zfmisc_1(A_297, B_298))) | ~m1_subset_1(C_299, k1_zfmisc_1(k2_zfmisc_1(A_297, B_298))))), inference(resolution, [status(thm)], [c_5167, c_2])).
% 14.40/6.57  tff(c_3253, plain, (![A_238, B_239, C_240, D_241]: (m1_subset_1('#skF_4'(A_238, B_239, C_240, D_241), B_239) | r2_relset_1(A_238, B_239, C_240, D_241) | ~m1_subset_1(D_241, k1_zfmisc_1(k2_zfmisc_1(A_238, B_239))) | ~m1_subset_1(C_240, k1_zfmisc_1(k2_zfmisc_1(A_238, B_239))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.40/6.57  tff(c_3305, plain, (![C_246]: (m1_subset_1('#skF_4'('#skF_5', '#skF_6', C_246, '#skF_8'), '#skF_6') | r2_relset_1('#skF_5', '#skF_6', C_246, '#skF_8') | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(resolution, [status(thm)], [c_74, c_3253])).
% 14.40/6.57  tff(c_3312, plain, (m1_subset_1('#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6') | r2_relset_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_80, c_3305])).
% 14.40/6.57  tff(c_3323, plain, (m1_subset_1('#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_70, c_3312])).
% 14.40/6.57  tff(c_50, plain, (![A_29, D_45, E_52, F_54, C_31, B_30]: (r2_hidden(k4_tarski(E_52, F_54), D_45) | ~r2_hidden(k4_tarski(E_52, F_54), C_31) | ~m1_subset_1(F_54, B_30) | ~m1_subset_1(E_52, A_29) | ~r2_relset_1(A_29, B_30, C_31, D_45) | ~m1_subset_1(D_45, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.40/6.57  tff(c_19963, plain, (![D_571, A_569, C_567, D_565, A_568, B_570, B_566]: (r2_hidden(k4_tarski('#skF_3'(A_569, B_570, C_567, D_571), '#skF_4'(A_569, B_570, C_567, D_571)), D_565) | ~m1_subset_1('#skF_4'(A_569, B_570, C_567, D_571), B_566) | ~m1_subset_1('#skF_3'(A_569, B_570, C_567, D_571), A_568) | ~r2_relset_1(A_568, B_566, D_571, D_565) | ~m1_subset_1(D_565, k1_zfmisc_1(k2_zfmisc_1(A_568, B_566))) | ~m1_subset_1(D_571, k1_zfmisc_1(k2_zfmisc_1(A_568, B_566))) | r2_hidden(k4_tarski('#skF_3'(A_569, B_570, C_567, D_571), '#skF_4'(A_569, B_570, C_567, D_571)), C_567) | r2_relset_1(A_569, B_570, C_567, D_571) | ~m1_subset_1(D_571, k1_zfmisc_1(k2_zfmisc_1(A_569, B_570))) | ~m1_subset_1(C_567, k1_zfmisc_1(k2_zfmisc_1(A_569, B_570))))), inference(resolution, [status(thm)], [c_5167, c_50])).
% 14.40/6.57  tff(c_19991, plain, (![D_565, A_568]: (r2_hidden(k4_tarski('#skF_3'('#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8')), D_565) | ~m1_subset_1('#skF_3'('#skF_5', '#skF_6', '#skF_7', '#skF_8'), A_568) | ~r2_relset_1(A_568, '#skF_6', '#skF_8', D_565) | ~m1_subset_1(D_565, k1_zfmisc_1(k2_zfmisc_1(A_568, '#skF_6'))) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(A_568, '#skF_6'))) | r2_hidden(k4_tarski('#skF_3'('#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8')), '#skF_7') | r2_relset_1('#skF_5', '#skF_6', '#skF_7', '#skF_8') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(resolution, [status(thm)], [c_3323, c_19963])).
% 14.40/6.57  tff(c_20039, plain, (![D_565, A_568]: (r2_hidden(k4_tarski('#skF_3'('#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8')), D_565) | ~m1_subset_1('#skF_3'('#skF_5', '#skF_6', '#skF_7', '#skF_8'), A_568) | ~r2_relset_1(A_568, '#skF_6', '#skF_8', D_565) | ~m1_subset_1(D_565, k1_zfmisc_1(k2_zfmisc_1(A_568, '#skF_6'))) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(A_568, '#skF_6'))) | r2_hidden(k4_tarski('#skF_3'('#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8')), '#skF_7') | r2_relset_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_74, c_19991])).
% 14.40/6.57  tff(c_20040, plain, (![D_565, A_568]: (r2_hidden(k4_tarski('#skF_3'('#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8')), D_565) | ~m1_subset_1('#skF_3'('#skF_5', '#skF_6', '#skF_7', '#skF_8'), A_568) | ~r2_relset_1(A_568, '#skF_6', '#skF_8', D_565) | ~m1_subset_1(D_565, k1_zfmisc_1(k2_zfmisc_1(A_568, '#skF_6'))) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(A_568, '#skF_6'))) | r2_hidden(k4_tarski('#skF_3'('#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8')), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_70, c_20039])).
% 14.40/6.57  tff(c_20475, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8')), '#skF_7')), inference(splitLeft, [status(thm)], [c_20040])).
% 14.40/6.57  tff(c_48, plain, (![A_29, D_45, E_52, F_54, C_31, B_30]: (r2_hidden(k4_tarski(E_52, F_54), C_31) | ~r2_hidden(k4_tarski(E_52, F_54), D_45) | ~m1_subset_1(F_54, B_30) | ~m1_subset_1(E_52, A_29) | ~r2_relset_1(A_29, B_30, C_31, D_45) | ~m1_subset_1(D_45, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.40/6.57  tff(c_21642, plain, (![B_606, A_605, C_603, D_608, C_607, A_604, B_602]: (r2_hidden(k4_tarski('#skF_3'(A_605, B_606, C_603, D_608), '#skF_4'(A_605, B_606, C_603, D_608)), C_607) | ~m1_subset_1('#skF_4'(A_605, B_606, C_603, D_608), B_602) | ~m1_subset_1('#skF_3'(A_605, B_606, C_603, D_608), A_604) | ~r2_relset_1(A_604, B_602, C_607, C_603) | ~m1_subset_1(C_603, k1_zfmisc_1(k2_zfmisc_1(A_604, B_602))) | ~m1_subset_1(C_607, k1_zfmisc_1(k2_zfmisc_1(A_604, B_602))) | r2_hidden(k4_tarski('#skF_3'(A_605, B_606, C_603, D_608), '#skF_4'(A_605, B_606, C_603, D_608)), D_608) | r2_relset_1(A_605, B_606, C_603, D_608) | ~m1_subset_1(D_608, k1_zfmisc_1(k2_zfmisc_1(A_605, B_606))) | ~m1_subset_1(C_603, k1_zfmisc_1(k2_zfmisc_1(A_605, B_606))))), inference(resolution, [status(thm)], [c_5167, c_48])).
% 14.40/6.57  tff(c_21670, plain, (![C_607, A_604]: (r2_hidden(k4_tarski('#skF_3'('#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8')), C_607) | ~m1_subset_1('#skF_3'('#skF_5', '#skF_6', '#skF_7', '#skF_8'), A_604) | ~r2_relset_1(A_604, '#skF_6', C_607, '#skF_7') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(A_604, '#skF_6'))) | ~m1_subset_1(C_607, k1_zfmisc_1(k2_zfmisc_1(A_604, '#skF_6'))) | r2_hidden(k4_tarski('#skF_3'('#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8')), '#skF_8') | r2_relset_1('#skF_5', '#skF_6', '#skF_7', '#skF_8') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(resolution, [status(thm)], [c_3323, c_21642])).
% 14.40/6.57  tff(c_21718, plain, (![C_607, A_604]: (r2_hidden(k4_tarski('#skF_3'('#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8')), C_607) | ~m1_subset_1('#skF_3'('#skF_5', '#skF_6', '#skF_7', '#skF_8'), A_604) | ~r2_relset_1(A_604, '#skF_6', C_607, '#skF_7') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(A_604, '#skF_6'))) | ~m1_subset_1(C_607, k1_zfmisc_1(k2_zfmisc_1(A_604, '#skF_6'))) | r2_hidden(k4_tarski('#skF_3'('#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8')), '#skF_8') | r2_relset_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_74, c_21670])).
% 14.40/6.57  tff(c_21719, plain, (![C_607, A_604]: (r2_hidden(k4_tarski('#skF_3'('#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8')), C_607) | ~m1_subset_1('#skF_3'('#skF_5', '#skF_6', '#skF_7', '#skF_8'), A_604) | ~r2_relset_1(A_604, '#skF_6', C_607, '#skF_7') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(A_604, '#skF_6'))) | ~m1_subset_1(C_607, k1_zfmisc_1(k2_zfmisc_1(A_604, '#skF_6'))) | r2_hidden(k4_tarski('#skF_3'('#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8')), '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_70, c_21718])).
% 14.40/6.57  tff(c_24872, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8')), '#skF_8')), inference(splitLeft, [status(thm)], [c_21719])).
% 14.40/6.57  tff(c_40, plain, (![A_29, B_30, C_31, D_45]: (~r2_hidden(k4_tarski('#skF_3'(A_29, B_30, C_31, D_45), '#skF_4'(A_29, B_30, C_31, D_45)), D_45) | ~r2_hidden(k4_tarski('#skF_3'(A_29, B_30, C_31, D_45), '#skF_4'(A_29, B_30, C_31, D_45)), C_31) | r2_relset_1(A_29, B_30, C_31, D_45) | ~m1_subset_1(D_45, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.40/6.57  tff(c_24874, plain, (~r2_hidden(k4_tarski('#skF_3'('#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8')), '#skF_7') | r2_relset_1('#skF_5', '#skF_6', '#skF_7', '#skF_8') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_24872, c_40])).
% 14.40/6.57  tff(c_24888, plain, (r2_relset_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_74, c_20475, c_24874])).
% 14.40/6.57  tff(c_24890, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_24888])).
% 14.40/6.57  tff(c_24892, plain, (~r2_hidden(k4_tarski('#skF_3'('#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8')), '#skF_8')), inference(splitRight, [status(thm)], [c_21719])).
% 14.40/6.57  tff(c_24899, plain, (![B_2]: (r2_hidden(k4_tarski('#skF_3'('#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8')), B_2) | ~r1_tarski('#skF_7', B_2) | r2_relset_1('#skF_5', '#skF_6', '#skF_7', '#skF_8') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(resolution, [status(thm)], [c_5219, c_24892])).
% 14.40/6.57  tff(c_24908, plain, (![B_2]: (r2_hidden(k4_tarski('#skF_3'('#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8')), B_2) | ~r1_tarski('#skF_7', B_2) | r2_relset_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_74, c_24899])).
% 14.40/6.57  tff(c_25297, plain, (![B_648]: (r2_hidden(k4_tarski('#skF_3'('#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8')), B_648) | ~r1_tarski('#skF_7', B_648))), inference(negUnitSimplification, [status(thm)], [c_70, c_24908])).
% 14.40/6.57  tff(c_25327, plain, (~r1_tarski('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_25297, c_24892])).
% 14.40/6.57  tff(c_27072, plain, (~r1_tarski('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_27054, c_25327])).
% 14.40/6.57  tff(c_27162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_185, c_27072])).
% 14.40/6.57  tff(c_27164, plain, (~r2_hidden(k4_tarski('#skF_3'('#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8')), '#skF_7')), inference(splitRight, [status(thm)], [c_20040])).
% 14.40/6.57  tff(c_27287, plain, (![B_2]: (r2_hidden(k4_tarski('#skF_3'('#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8')), B_2) | ~r1_tarski('#skF_8', B_2) | r2_relset_1('#skF_5', '#skF_6', '#skF_7', '#skF_8') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(resolution, [status(thm)], [c_5227, c_27164])).
% 14.40/6.57  tff(c_27301, plain, (![B_2]: (r2_hidden(k4_tarski('#skF_3'('#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8')), B_2) | ~r1_tarski('#skF_8', B_2) | r2_relset_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_74, c_27287])).
% 14.40/6.57  tff(c_27709, plain, (![B_697]: (r2_hidden(k4_tarski('#skF_3'('#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8')), B_697) | ~r1_tarski('#skF_8', B_697))), inference(negUnitSimplification, [status(thm)], [c_70, c_27301])).
% 14.40/6.57  tff(c_27739, plain, (~r1_tarski('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_27709, c_27164])).
% 14.40/6.57  tff(c_34008, plain, (~r1_tarski('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_33991, c_27739])).
% 14.40/6.57  tff(c_34089, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_185, c_34008])).
% 14.40/6.57  tff(c_34090, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_2254])).
% 14.40/6.57  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 14.40/6.57  tff(c_34123, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34090, c_8])).
% 14.40/6.57  tff(c_16, plain, (![A_10]: (k2_zfmisc_1(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 14.40/6.57  tff(c_34121, plain, (![A_10]: (k2_zfmisc_1(A_10, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34090, c_34090, c_16])).
% 14.40/6.57  tff(c_463, plain, (![C_121, B_122, A_123]: (~v1_xboole_0(C_121) | ~m1_subset_1(B_122, k1_zfmisc_1(C_121)) | ~r2_hidden(A_123, B_122))), inference(cnfTransformation, [status(thm)], [f_62])).
% 14.40/6.57  tff(c_478, plain, (![A_123]: (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6')) | ~r2_hidden(A_123, '#skF_7'))), inference(resolution, [status(thm)], [c_80, c_463])).
% 14.40/6.57  tff(c_538, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_478])).
% 14.40/6.57  tff(c_34385, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34121, c_538])).
% 14.40/6.57  tff(c_34394, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34123, c_34385])).
% 14.40/6.57  tff(c_34395, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_2251])).
% 14.40/6.57  tff(c_34429, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34395, c_8])).
% 14.40/6.57  tff(c_34427, plain, (![A_10]: (k2_zfmisc_1(A_10, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34395, c_34395, c_16])).
% 14.40/6.57  tff(c_34696, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34427, c_538])).
% 14.40/6.57  tff(c_34705, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34429, c_34696])).
% 14.40/6.57  tff(c_34707, plain, (v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_478])).
% 14.40/6.57  tff(c_479, plain, (![A_123]: (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6')) | ~r2_hidden(A_123, '#skF_8'))), inference(resolution, [status(thm)], [c_74, c_463])).
% 14.40/6.57  tff(c_34708, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_479])).
% 14.40/6.57  tff(c_34809, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34707, c_34708])).
% 14.40/6.57  tff(c_34818, plain, (![A_826]: (~r2_hidden(A_826, '#skF_8'))), inference(splitRight, [status(thm)], [c_479])).
% 14.40/6.57  tff(c_34823, plain, (![B_2]: (r1_tarski('#skF_8', B_2))), inference(resolution, [status(thm)], [c_6, c_34818])).
% 14.40/6.57  tff(c_34812, plain, (![A_825]: (~r2_hidden(A_825, '#skF_7'))), inference(splitRight, [status(thm)], [c_478])).
% 14.40/6.57  tff(c_34825, plain, (![B_827]: (r1_tarski('#skF_7', B_827))), inference(resolution, [status(thm)], [c_6, c_34812])).
% 14.40/6.57  tff(c_12, plain, (![A_9]: (k1_xboole_0=A_9 | ~r1_tarski(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.40/6.57  tff(c_34863, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_34825, c_12])).
% 14.40/6.57  tff(c_35128, plain, (![A_838]: (A_838='#skF_7' | ~r1_tarski(A_838, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_34863, c_34863, c_12])).
% 14.40/6.57  tff(c_35153, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_34823, c_35128])).
% 14.40/6.57  tff(c_35180, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_35153, c_70])).
% 14.40/6.57  tff(c_35189, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_35056, c_35180])).
% 14.40/6.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.40/6.57  
% 14.40/6.57  Inference rules
% 14.40/6.57  ----------------------
% 14.40/6.57  #Ref     : 1
% 14.40/6.57  #Sup     : 8407
% 14.40/6.57  #Fact    : 6
% 14.40/6.57  #Define  : 0
% 14.40/6.57  #Split   : 32
% 14.40/6.57  #Chain   : 0
% 14.40/6.57  #Close   : 0
% 14.40/6.57  
% 14.40/6.57  Ordering : KBO
% 14.40/6.57  
% 14.40/6.57  Simplification rules
% 14.40/6.57  ----------------------
% 14.40/6.57  #Subsume      : 2176
% 14.40/6.57  #Demod        : 13476
% 14.40/6.57  #Tautology    : 4268
% 14.40/6.57  #SimpNegUnit  : 94
% 14.40/6.57  #BackRed      : 625
% 14.40/6.57  
% 14.40/6.57  #Partial instantiations: 0
% 14.40/6.57  #Strategies tried      : 1
% 14.40/6.57  
% 14.40/6.57  Timing (in seconds)
% 14.40/6.57  ----------------------
% 14.71/6.58  Preprocessing        : 0.34
% 14.71/6.58  Parsing              : 0.18
% 14.71/6.58  CNF conversion       : 0.03
% 14.71/6.58  Main loop            : 5.45
% 14.71/6.58  Inferencing          : 1.01
% 14.71/6.58  Reduction            : 2.52
% 14.71/6.58  Demodulation         : 2.06
% 14.71/6.58  BG Simplification    : 0.12
% 14.71/6.58  Subsumption          : 1.52
% 14.71/6.58  Abstraction          : 0.18
% 14.71/6.58  MUC search           : 0.00
% 14.71/6.58  Cooper               : 0.00
% 14.71/6.58  Total                : 5.85
% 14.71/6.58  Index Insertion      : 0.00
% 14.71/6.58  Index Deletion       : 0.00
% 14.71/6.58  Index Matching       : 0.00
% 14.71/6.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
