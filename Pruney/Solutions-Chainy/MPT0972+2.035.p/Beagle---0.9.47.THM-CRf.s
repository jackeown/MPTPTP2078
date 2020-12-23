%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:39 EST 2020

% Result     : Theorem 5.78s
% Output     : CNFRefutation 5.78s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 993 expanded)
%              Number of leaves         :   36 ( 345 expanded)
%              Depth                    :   12
%              Number of atoms          :  230 (2673 expanded)
%              Number of equality atoms :   82 ( 447 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_131,negated_conjecture,(
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

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_110,axiom,(
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

tff(f_78,axiom,(
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

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_54,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_54,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_60,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1118,plain,(
    ! [A_155,B_156,C_157,D_158] :
      ( r2_relset_1(A_155,B_156,C_157,C_157)
      | ~ m1_subset_1(D_158,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156)))
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1143,plain,(
    ! [C_159] :
      ( r2_relset_1('#skF_5','#skF_6',C_159,C_159)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_60,c_1118])).

tff(c_1164,plain,(
    r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_54,c_1143])).

tff(c_100,plain,(
    ! [C_49,A_50,B_51] :
      ( v1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_115,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_100])).

tff(c_64,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_62,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_512,plain,(
    ! [A_103,B_104,C_105] :
      ( k1_relset_1(A_103,B_104,C_105) = k1_relat_1(C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_534,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_512])).

tff(c_1233,plain,(
    ! [B_169,A_170,C_171] :
      ( k1_xboole_0 = B_169
      | k1_relset_1(A_170,B_169,C_171) = A_170
      | ~ v1_funct_2(C_171,A_170,B_169)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(A_170,B_169))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1248,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_1233])).

tff(c_1267,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_534,c_1248])).

tff(c_1274,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1267])).

tff(c_116,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_54,c_100])).

tff(c_58,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_56,plain,(
    v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_535,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_54,c_512])).

tff(c_1251,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_1233])).

tff(c_1270,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_535,c_1251])).

tff(c_1280,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1270])).

tff(c_1334,plain,(
    ! [A_175,B_176] :
      ( r2_hidden('#skF_4'(A_175,B_176),k1_relat_1(A_175))
      | B_176 = A_175
      | k1_relat_1(B_176) != k1_relat_1(A_175)
      | ~ v1_funct_1(B_176)
      | ~ v1_relat_1(B_176)
      | ~ v1_funct_1(A_175)
      | ~ v1_relat_1(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1342,plain,(
    ! [B_176] :
      ( r2_hidden('#skF_4'('#skF_8',B_176),'#skF_5')
      | B_176 = '#skF_8'
      | k1_relat_1(B_176) != k1_relat_1('#skF_8')
      | ~ v1_funct_1(B_176)
      | ~ v1_relat_1(B_176)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1280,c_1334])).

tff(c_2871,plain,(
    ! [B_266] :
      ( r2_hidden('#skF_4'('#skF_8',B_266),'#skF_5')
      | B_266 = '#skF_8'
      | k1_relat_1(B_266) != '#skF_5'
      | ~ v1_funct_1(B_266)
      | ~ v1_relat_1(B_266) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_58,c_1280,c_1342])).

tff(c_52,plain,(
    ! [E_41] :
      ( k1_funct_1('#skF_7',E_41) = k1_funct_1('#skF_8',E_41)
      | ~ r2_hidden(E_41,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_2892,plain,(
    ! [B_273] :
      ( k1_funct_1('#skF_7','#skF_4'('#skF_8',B_273)) = k1_funct_1('#skF_8','#skF_4'('#skF_8',B_273))
      | B_273 = '#skF_8'
      | k1_relat_1(B_273) != '#skF_5'
      | ~ v1_funct_1(B_273)
      | ~ v1_relat_1(B_273) ) ),
    inference(resolution,[status(thm)],[c_2871,c_52])).

tff(c_28,plain,(
    ! [B_22,A_18] :
      ( k1_funct_1(B_22,'#skF_4'(A_18,B_22)) != k1_funct_1(A_18,'#skF_4'(A_18,B_22))
      | B_22 = A_18
      | k1_relat_1(B_22) != k1_relat_1(A_18)
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2899,plain,
    ( k1_relat_1('#skF_7') != k1_relat_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | '#skF_7' = '#skF_8'
    | k1_relat_1('#skF_7') != '#skF_5'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2892,c_28])).

tff(c_2906,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_64,c_1274,c_116,c_58,c_1274,c_1280,c_2899])).

tff(c_50,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_2932,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2906,c_50])).

tff(c_2942,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1164,c_2932])).

tff(c_2943,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1270])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2977,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2943,c_6])).

tff(c_18,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2975,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2943,c_2943,c_18])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_159,plain,(
    ! [C_62,A_63,B_64] :
      ( r2_hidden(C_62,A_63)
      | ~ r2_hidden(C_62,B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_164,plain,(
    ! [A_66,A_67] :
      ( r2_hidden('#skF_1'(A_66),A_67)
      | ~ m1_subset_1(A_66,k1_zfmisc_1(A_67))
      | v1_xboole_0(A_66) ) ),
    inference(resolution,[status(thm)],[c_4,c_159])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_181,plain,(
    ! [A_68,A_69] :
      ( ~ v1_xboole_0(A_68)
      | ~ m1_subset_1(A_69,k1_zfmisc_1(A_68))
      | v1_xboole_0(A_69) ) ),
    inference(resolution,[status(thm)],[c_164,c_2])).

tff(c_191,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6'))
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_181])).

tff(c_195,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_191])).

tff(c_3055,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2975,c_195])).

tff(c_3062,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2977,c_3055])).

tff(c_3063,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1267])).

tff(c_3097,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3063,c_6])).

tff(c_3095,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3063,c_3063,c_18])).

tff(c_3170,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3095,c_195])).

tff(c_3177,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3097,c_3170])).

tff(c_3179,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_191])).

tff(c_192,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6'))
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_54,c_181])).

tff(c_3181,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3179,c_192])).

tff(c_4155,plain,(
    ! [A_401,B_402] :
      ( r2_hidden('#skF_2'(A_401,B_402),B_402)
      | r2_hidden('#skF_3'(A_401,B_402),A_401)
      | B_402 = A_401 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4191,plain,(
    ! [B_403,A_404] :
      ( ~ v1_xboole_0(B_403)
      | r2_hidden('#skF_3'(A_404,B_403),A_404)
      | B_403 = A_404 ) ),
    inference(resolution,[status(thm)],[c_4155,c_2])).

tff(c_4214,plain,(
    ! [A_405,B_406] :
      ( ~ v1_xboole_0(A_405)
      | ~ v1_xboole_0(B_406)
      | B_406 = A_405 ) ),
    inference(resolution,[status(thm)],[c_4191,c_2])).

tff(c_4227,plain,(
    ! [B_407] :
      ( ~ v1_xboole_0(B_407)
      | k1_xboole_0 = B_407 ) ),
    inference(resolution,[status(thm)],[c_6,c_4214])).

tff(c_4240,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_3181,c_4227])).

tff(c_24,plain,(
    ! [A_14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4260,plain,(
    ! [A_14] : m1_subset_1('#skF_8',k1_zfmisc_1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4240,c_24])).

tff(c_4435,plain,(
    ! [A_422,B_423,C_424,D_425] :
      ( r2_relset_1(A_422,B_423,C_424,C_424)
      | ~ m1_subset_1(D_425,k1_zfmisc_1(k2_zfmisc_1(A_422,B_423)))
      | ~ m1_subset_1(C_424,k1_zfmisc_1(k2_zfmisc_1(A_422,B_423))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_4669,plain,(
    ! [A_452,B_453,C_454] :
      ( r2_relset_1(A_452,B_453,C_454,C_454)
      | ~ m1_subset_1(C_454,k1_zfmisc_1(k2_zfmisc_1(A_452,B_453))) ) ),
    inference(resolution,[status(thm)],[c_4260,c_4435])).

tff(c_4681,plain,(
    ! [A_452,B_453] : r2_relset_1(A_452,B_453,'#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_4260,c_4669])).

tff(c_4241,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3179,c_4227])).

tff(c_4303,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4240,c_4241])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( k1_xboole_0 = B_9
      | k1_xboole_0 = A_8
      | k2_zfmisc_1(A_8,B_9) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4450,plain,(
    ! [B_426,A_427] :
      ( B_426 = '#skF_8'
      | A_427 = '#skF_8'
      | k2_zfmisc_1(A_427,B_426) != '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4240,c_4240,c_4240,c_16])).

tff(c_4464,plain,
    ( '#skF_6' = '#skF_8'
    | '#skF_5' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_4303,c_4450])).

tff(c_4465,plain,(
    '#skF_5' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_4464])).

tff(c_3346,plain,(
    ! [A_305,B_306] :
      ( r2_hidden('#skF_2'(A_305,B_306),B_306)
      | r2_hidden('#skF_3'(A_305,B_306),A_305)
      | B_306 = A_305 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3390,plain,(
    ! [B_309,A_310] :
      ( ~ v1_xboole_0(B_309)
      | r2_hidden('#skF_3'(A_310,B_309),A_310)
      | B_309 = A_310 ) ),
    inference(resolution,[status(thm)],[c_3346,c_2])).

tff(c_3413,plain,(
    ! [A_311,B_312] :
      ( ~ v1_xboole_0(A_311)
      | ~ v1_xboole_0(B_312)
      | B_312 = A_311 ) ),
    inference(resolution,[status(thm)],[c_3390,c_2])).

tff(c_3429,plain,(
    ! [B_313] :
      ( ~ v1_xboole_0(B_313)
      | k1_xboole_0 = B_313 ) ),
    inference(resolution,[status(thm)],[c_6,c_3413])).

tff(c_3446,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_3181,c_3429])).

tff(c_3476,plain,(
    ! [A_14] : m1_subset_1('#skF_8',k1_zfmisc_1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3446,c_24])).

tff(c_3643,plain,(
    ! [A_330,B_331,C_332,D_333] :
      ( r2_relset_1(A_330,B_331,C_332,C_332)
      | ~ m1_subset_1(D_333,k1_zfmisc_1(k2_zfmisc_1(A_330,B_331)))
      | ~ m1_subset_1(C_332,k1_zfmisc_1(k2_zfmisc_1(A_330,B_331))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_3971,plain,(
    ! [A_375,B_376,C_377] :
      ( r2_relset_1(A_375,B_376,C_377,C_377)
      | ~ m1_subset_1(C_377,k1_zfmisc_1(k2_zfmisc_1(A_375,B_376))) ) ),
    inference(resolution,[status(thm)],[c_3476,c_3643])).

tff(c_3983,plain,(
    ! [A_375,B_376] : r2_relset_1(A_375,B_376,'#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_3476,c_3971])).

tff(c_129,plain,(
    ! [E_54] :
      ( k1_funct_1('#skF_7',E_54) = k1_funct_1('#skF_8',E_54)
      | ~ r2_hidden(E_54,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_134,plain,
    ( k1_funct_1('#skF_7','#skF_1'('#skF_5')) = k1_funct_1('#skF_8','#skF_1'('#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_129])).

tff(c_3182,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_3445,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3182,c_3429])).

tff(c_3507,plain,(
    '#skF_5' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3446,c_3445])).

tff(c_3178,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_191])).

tff(c_3448,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_3178,c_3429])).

tff(c_3484,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3446,c_3448])).

tff(c_3494,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3484,c_50])).

tff(c_3587,plain,(
    ~ r2_relset_1('#skF_8','#skF_6','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3507,c_3494])).

tff(c_3986,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3983,c_3587])).

tff(c_3988,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_4486,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4465,c_3988])).

tff(c_4491,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3181,c_4486])).

tff(c_4492,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_4464])).

tff(c_4242,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_3178,c_4227])).

tff(c_4270,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4240,c_4242])).

tff(c_4280,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4270,c_50])).

tff(c_4494,plain,(
    ~ r2_relset_1('#skF_5','#skF_8','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4492,c_4280])).

tff(c_4693,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4681,c_4494])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:20:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.78/2.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.78/2.14  
% 5.78/2.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.78/2.14  %$ r2_relset_1 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_4
% 5.78/2.14  
% 5.78/2.14  %Foreground sorts:
% 5.78/2.14  
% 5.78/2.14  
% 5.78/2.14  %Background operators:
% 5.78/2.14  
% 5.78/2.14  
% 5.78/2.14  %Foreground operators:
% 5.78/2.14  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.78/2.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.78/2.14  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.78/2.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.78/2.14  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.78/2.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.78/2.14  tff('#skF_7', type, '#skF_7': $i).
% 5.78/2.14  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.78/2.14  tff('#skF_5', type, '#skF_5': $i).
% 5.78/2.14  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.78/2.14  tff('#skF_6', type, '#skF_6': $i).
% 5.78/2.14  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.78/2.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.78/2.14  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.78/2.14  tff('#skF_8', type, '#skF_8': $i).
% 5.78/2.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.78/2.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.78/2.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.78/2.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.78/2.14  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.78/2.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.78/2.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.78/2.14  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.78/2.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.78/2.14  
% 5.78/2.16  tff(f_131, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_2)).
% 5.78/2.16  tff(f_92, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 5.78/2.16  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.78/2.16  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.78/2.16  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.78/2.16  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 5.78/2.16  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.78/2.16  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.78/2.16  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.78/2.16  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 5.78/2.16  tff(f_39, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 5.78/2.16  tff(f_54, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 5.78/2.16  tff(c_54, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.78/2.16  tff(c_60, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.78/2.16  tff(c_1118, plain, (![A_155, B_156, C_157, D_158]: (r2_relset_1(A_155, B_156, C_157, C_157) | ~m1_subset_1(D_158, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.78/2.16  tff(c_1143, plain, (![C_159]: (r2_relset_1('#skF_5', '#skF_6', C_159, C_159) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(resolution, [status(thm)], [c_60, c_1118])).
% 5.78/2.16  tff(c_1164, plain, (r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_54, c_1143])).
% 5.78/2.16  tff(c_100, plain, (![C_49, A_50, B_51]: (v1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.78/2.16  tff(c_115, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_60, c_100])).
% 5.78/2.16  tff(c_64, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.78/2.16  tff(c_62, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.78/2.16  tff(c_512, plain, (![A_103, B_104, C_105]: (k1_relset_1(A_103, B_104, C_105)=k1_relat_1(C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.78/2.16  tff(c_534, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_60, c_512])).
% 5.78/2.16  tff(c_1233, plain, (![B_169, A_170, C_171]: (k1_xboole_0=B_169 | k1_relset_1(A_170, B_169, C_171)=A_170 | ~v1_funct_2(C_171, A_170, B_169) | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(A_170, B_169))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.78/2.16  tff(c_1248, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_5' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_60, c_1233])).
% 5.78/2.16  tff(c_1267, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_534, c_1248])).
% 5.78/2.16  tff(c_1274, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitLeft, [status(thm)], [c_1267])).
% 5.78/2.16  tff(c_116, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_54, c_100])).
% 5.78/2.17  tff(c_58, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.78/2.17  tff(c_56, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.78/2.17  tff(c_535, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_54, c_512])).
% 5.78/2.17  tff(c_1251, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_54, c_1233])).
% 5.78/2.17  tff(c_1270, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_535, c_1251])).
% 5.78/2.17  tff(c_1280, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_1270])).
% 5.78/2.17  tff(c_1334, plain, (![A_175, B_176]: (r2_hidden('#skF_4'(A_175, B_176), k1_relat_1(A_175)) | B_176=A_175 | k1_relat_1(B_176)!=k1_relat_1(A_175) | ~v1_funct_1(B_176) | ~v1_relat_1(B_176) | ~v1_funct_1(A_175) | ~v1_relat_1(A_175))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.78/2.17  tff(c_1342, plain, (![B_176]: (r2_hidden('#skF_4'('#skF_8', B_176), '#skF_5') | B_176='#skF_8' | k1_relat_1(B_176)!=k1_relat_1('#skF_8') | ~v1_funct_1(B_176) | ~v1_relat_1(B_176) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1280, c_1334])).
% 5.78/2.17  tff(c_2871, plain, (![B_266]: (r2_hidden('#skF_4'('#skF_8', B_266), '#skF_5') | B_266='#skF_8' | k1_relat_1(B_266)!='#skF_5' | ~v1_funct_1(B_266) | ~v1_relat_1(B_266))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_58, c_1280, c_1342])).
% 5.78/2.17  tff(c_52, plain, (![E_41]: (k1_funct_1('#skF_7', E_41)=k1_funct_1('#skF_8', E_41) | ~r2_hidden(E_41, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.78/2.17  tff(c_2892, plain, (![B_273]: (k1_funct_1('#skF_7', '#skF_4'('#skF_8', B_273))=k1_funct_1('#skF_8', '#skF_4'('#skF_8', B_273)) | B_273='#skF_8' | k1_relat_1(B_273)!='#skF_5' | ~v1_funct_1(B_273) | ~v1_relat_1(B_273))), inference(resolution, [status(thm)], [c_2871, c_52])).
% 5.78/2.17  tff(c_28, plain, (![B_22, A_18]: (k1_funct_1(B_22, '#skF_4'(A_18, B_22))!=k1_funct_1(A_18, '#skF_4'(A_18, B_22)) | B_22=A_18 | k1_relat_1(B_22)!=k1_relat_1(A_18) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.78/2.17  tff(c_2899, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | '#skF_7'='#skF_8' | k1_relat_1('#skF_7')!='#skF_5' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2892, c_28])).
% 5.78/2.17  tff(c_2906, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_115, c_64, c_1274, c_116, c_58, c_1274, c_1280, c_2899])).
% 5.78/2.17  tff(c_50, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.78/2.17  tff(c_2932, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2906, c_50])).
% 5.78/2.17  tff(c_2942, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1164, c_2932])).
% 5.78/2.17  tff(c_2943, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_1270])).
% 5.78/2.17  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.78/2.17  tff(c_2977, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2943, c_6])).
% 5.78/2.17  tff(c_18, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.78/2.17  tff(c_2975, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2943, c_2943, c_18])).
% 5.78/2.17  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.78/2.17  tff(c_159, plain, (![C_62, A_63, B_64]: (r2_hidden(C_62, A_63) | ~r2_hidden(C_62, B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.78/2.17  tff(c_164, plain, (![A_66, A_67]: (r2_hidden('#skF_1'(A_66), A_67) | ~m1_subset_1(A_66, k1_zfmisc_1(A_67)) | v1_xboole_0(A_66))), inference(resolution, [status(thm)], [c_4, c_159])).
% 5.78/2.17  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.78/2.17  tff(c_181, plain, (![A_68, A_69]: (~v1_xboole_0(A_68) | ~m1_subset_1(A_69, k1_zfmisc_1(A_68)) | v1_xboole_0(A_69))), inference(resolution, [status(thm)], [c_164, c_2])).
% 5.78/2.17  tff(c_191, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6')) | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_60, c_181])).
% 5.78/2.17  tff(c_195, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_191])).
% 5.78/2.17  tff(c_3055, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2975, c_195])).
% 5.78/2.17  tff(c_3062, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2977, c_3055])).
% 5.78/2.17  tff(c_3063, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_1267])).
% 5.78/2.17  tff(c_3097, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3063, c_6])).
% 5.78/2.17  tff(c_3095, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3063, c_3063, c_18])).
% 5.78/2.17  tff(c_3170, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3095, c_195])).
% 5.78/2.17  tff(c_3177, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3097, c_3170])).
% 5.78/2.17  tff(c_3179, plain, (v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_191])).
% 5.78/2.17  tff(c_192, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6')) | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_54, c_181])).
% 5.78/2.17  tff(c_3181, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_3179, c_192])).
% 5.78/2.17  tff(c_4155, plain, (![A_401, B_402]: (r2_hidden('#skF_2'(A_401, B_402), B_402) | r2_hidden('#skF_3'(A_401, B_402), A_401) | B_402=A_401)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.78/2.17  tff(c_4191, plain, (![B_403, A_404]: (~v1_xboole_0(B_403) | r2_hidden('#skF_3'(A_404, B_403), A_404) | B_403=A_404)), inference(resolution, [status(thm)], [c_4155, c_2])).
% 5.78/2.17  tff(c_4214, plain, (![A_405, B_406]: (~v1_xboole_0(A_405) | ~v1_xboole_0(B_406) | B_406=A_405)), inference(resolution, [status(thm)], [c_4191, c_2])).
% 5.78/2.17  tff(c_4227, plain, (![B_407]: (~v1_xboole_0(B_407) | k1_xboole_0=B_407)), inference(resolution, [status(thm)], [c_6, c_4214])).
% 5.78/2.17  tff(c_4240, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_3181, c_4227])).
% 5.78/2.17  tff(c_24, plain, (![A_14]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.78/2.17  tff(c_4260, plain, (![A_14]: (m1_subset_1('#skF_8', k1_zfmisc_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_4240, c_24])).
% 5.78/2.17  tff(c_4435, plain, (![A_422, B_423, C_424, D_425]: (r2_relset_1(A_422, B_423, C_424, C_424) | ~m1_subset_1(D_425, k1_zfmisc_1(k2_zfmisc_1(A_422, B_423))) | ~m1_subset_1(C_424, k1_zfmisc_1(k2_zfmisc_1(A_422, B_423))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.78/2.17  tff(c_4669, plain, (![A_452, B_453, C_454]: (r2_relset_1(A_452, B_453, C_454, C_454) | ~m1_subset_1(C_454, k1_zfmisc_1(k2_zfmisc_1(A_452, B_453))))), inference(resolution, [status(thm)], [c_4260, c_4435])).
% 5.78/2.17  tff(c_4681, plain, (![A_452, B_453]: (r2_relset_1(A_452, B_453, '#skF_8', '#skF_8'))), inference(resolution, [status(thm)], [c_4260, c_4669])).
% 5.78/2.17  tff(c_4241, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_3179, c_4227])).
% 5.78/2.17  tff(c_4303, plain, (k2_zfmisc_1('#skF_5', '#skF_6')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_4240, c_4241])).
% 5.78/2.17  tff(c_16, plain, (![B_9, A_8]: (k1_xboole_0=B_9 | k1_xboole_0=A_8 | k2_zfmisc_1(A_8, B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.78/2.17  tff(c_4450, plain, (![B_426, A_427]: (B_426='#skF_8' | A_427='#skF_8' | k2_zfmisc_1(A_427, B_426)!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4240, c_4240, c_4240, c_16])).
% 5.78/2.17  tff(c_4464, plain, ('#skF_6'='#skF_8' | '#skF_5'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_4303, c_4450])).
% 5.78/2.17  tff(c_4465, plain, ('#skF_5'='#skF_8'), inference(splitLeft, [status(thm)], [c_4464])).
% 5.78/2.17  tff(c_3346, plain, (![A_305, B_306]: (r2_hidden('#skF_2'(A_305, B_306), B_306) | r2_hidden('#skF_3'(A_305, B_306), A_305) | B_306=A_305)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.78/2.17  tff(c_3390, plain, (![B_309, A_310]: (~v1_xboole_0(B_309) | r2_hidden('#skF_3'(A_310, B_309), A_310) | B_309=A_310)), inference(resolution, [status(thm)], [c_3346, c_2])).
% 5.78/2.17  tff(c_3413, plain, (![A_311, B_312]: (~v1_xboole_0(A_311) | ~v1_xboole_0(B_312) | B_312=A_311)), inference(resolution, [status(thm)], [c_3390, c_2])).
% 5.78/2.17  tff(c_3429, plain, (![B_313]: (~v1_xboole_0(B_313) | k1_xboole_0=B_313)), inference(resolution, [status(thm)], [c_6, c_3413])).
% 5.78/2.17  tff(c_3446, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_3181, c_3429])).
% 5.78/2.17  tff(c_3476, plain, (![A_14]: (m1_subset_1('#skF_8', k1_zfmisc_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_3446, c_24])).
% 5.78/2.17  tff(c_3643, plain, (![A_330, B_331, C_332, D_333]: (r2_relset_1(A_330, B_331, C_332, C_332) | ~m1_subset_1(D_333, k1_zfmisc_1(k2_zfmisc_1(A_330, B_331))) | ~m1_subset_1(C_332, k1_zfmisc_1(k2_zfmisc_1(A_330, B_331))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.78/2.17  tff(c_3971, plain, (![A_375, B_376, C_377]: (r2_relset_1(A_375, B_376, C_377, C_377) | ~m1_subset_1(C_377, k1_zfmisc_1(k2_zfmisc_1(A_375, B_376))))), inference(resolution, [status(thm)], [c_3476, c_3643])).
% 5.78/2.17  tff(c_3983, plain, (![A_375, B_376]: (r2_relset_1(A_375, B_376, '#skF_8', '#skF_8'))), inference(resolution, [status(thm)], [c_3476, c_3971])).
% 5.78/2.17  tff(c_129, plain, (![E_54]: (k1_funct_1('#skF_7', E_54)=k1_funct_1('#skF_8', E_54) | ~r2_hidden(E_54, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.78/2.17  tff(c_134, plain, (k1_funct_1('#skF_7', '#skF_1'('#skF_5'))=k1_funct_1('#skF_8', '#skF_1'('#skF_5')) | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_129])).
% 5.78/2.17  tff(c_3182, plain, (v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_134])).
% 5.78/2.17  tff(c_3445, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_3182, c_3429])).
% 5.78/2.17  tff(c_3507, plain, ('#skF_5'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_3446, c_3445])).
% 5.78/2.17  tff(c_3178, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_191])).
% 5.78/2.17  tff(c_3448, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_3178, c_3429])).
% 5.78/2.17  tff(c_3484, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_3446, c_3448])).
% 5.78/2.17  tff(c_3494, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_3484, c_50])).
% 5.78/2.17  tff(c_3587, plain, (~r2_relset_1('#skF_8', '#skF_6', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_3507, c_3494])).
% 5.78/2.17  tff(c_3986, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3983, c_3587])).
% 5.78/2.17  tff(c_3988, plain, (~v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_134])).
% 5.78/2.17  tff(c_4486, plain, (~v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4465, c_3988])).
% 5.78/2.17  tff(c_4491, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3181, c_4486])).
% 5.78/2.17  tff(c_4492, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_4464])).
% 5.78/2.17  tff(c_4242, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_3178, c_4227])).
% 5.78/2.17  tff(c_4270, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_4240, c_4242])).
% 5.78/2.17  tff(c_4280, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4270, c_50])).
% 5.78/2.17  tff(c_4494, plain, (~r2_relset_1('#skF_5', '#skF_8', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4492, c_4280])).
% 5.78/2.17  tff(c_4693, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4681, c_4494])).
% 5.78/2.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.78/2.17  
% 5.78/2.17  Inference rules
% 5.78/2.17  ----------------------
% 5.78/2.17  #Ref     : 2
% 5.78/2.17  #Sup     : 912
% 5.78/2.17  #Fact    : 0
% 5.78/2.17  #Define  : 0
% 5.78/2.17  #Split   : 21
% 5.78/2.17  #Chain   : 0
% 5.78/2.17  #Close   : 0
% 5.78/2.17  
% 5.78/2.17  Ordering : KBO
% 5.78/2.17  
% 5.78/2.17  Simplification rules
% 5.78/2.17  ----------------------
% 5.78/2.17  #Subsume      : 347
% 5.78/2.17  #Demod        : 631
% 5.78/2.17  #Tautology    : 316
% 5.78/2.17  #SimpNegUnit  : 105
% 5.78/2.17  #BackRed      : 287
% 5.78/2.17  
% 5.78/2.17  #Partial instantiations: 0
% 5.78/2.17  #Strategies tried      : 1
% 5.78/2.17  
% 5.78/2.17  Timing (in seconds)
% 5.78/2.17  ----------------------
% 5.78/2.17  Preprocessing        : 0.35
% 5.78/2.17  Parsing              : 0.18
% 5.78/2.17  CNF conversion       : 0.02
% 5.78/2.17  Main loop            : 0.98
% 5.78/2.17  Inferencing          : 0.32
% 5.78/2.17  Reduction            : 0.29
% 5.78/2.17  Demodulation         : 0.19
% 5.78/2.17  BG Simplification    : 0.05
% 5.78/2.17  Subsumption          : 0.23
% 5.78/2.17  Abstraction          : 0.05
% 5.78/2.17  MUC search           : 0.00
% 5.78/2.17  Cooper               : 0.00
% 5.78/2.17  Total                : 1.37
% 6.03/2.17  Index Insertion      : 0.00
% 6.03/2.17  Index Deletion       : 0.00
% 6.03/2.17  Index Matching       : 0.00
% 6.03/2.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
