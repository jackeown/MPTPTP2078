%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:33 EST 2020

% Result     : Theorem 4.41s
% Output     : CNFRefutation 4.48s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 440 expanded)
%              Number of leaves         :   41 ( 168 expanded)
%              Depth                    :   11
%              Number of atoms          :  250 (1221 expanded)
%              Number of equality atoms :   18 (  52 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_relset_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_6 > #skF_1 > #skF_11 > #skF_15 > #skF_4 > #skF_10 > #skF_14 > #skF_13 > #skF_2 > #skF_9 > #skF_3 > #skF_8 > #skF_7 > #skF_5 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_60,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_114,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ~ v1_xboole_0(C)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
                   => ! [E] :
                        ( m1_subset_1(E,A)
                       => ( r2_hidden(E,k7_relset_1(C,A,D,B))
                        <=> ? [F] :
                              ( m1_subset_1(F,C)
                              & r2_hidden(k4_tarski(F,E),D)
                              & r2_hidden(F,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relset_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( v1_relat_1(C)
         => ( C = k7_relat_1(A,B)
          <=> ! [D,E] :
                ( r2_hidden(k4_tarski(D,E),C)
              <=> ( r2_hidden(D,B)
                  & r2_hidden(k4_tarski(D,E),A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_36,plain,(
    ! [A_44,B_45] : v1_relat_1(k2_zfmisc_1(A_44,B_45)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_56,plain,(
    m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1('#skF_12','#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_81,plain,(
    ! [B_154,A_155] :
      ( v1_relat_1(B_154)
      | ~ m1_subset_1(B_154,k1_zfmisc_1(A_155))
      | ~ v1_relat_1(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_84,plain,
    ( v1_relat_1('#skF_13')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_12','#skF_10')) ),
    inference(resolution,[status(thm)],[c_56,c_81])).

tff(c_87,plain,(
    v1_relat_1('#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_84])).

tff(c_1996,plain,(
    ! [A_406,B_407,C_408,D_409] :
      ( k7_relset_1(A_406,B_407,C_408,D_409) = k9_relat_1(C_408,D_409)
      | ~ m1_subset_1(C_408,k1_zfmisc_1(k2_zfmisc_1(A_406,B_407))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2003,plain,(
    ! [D_409] : k7_relset_1('#skF_12','#skF_10','#skF_13',D_409) = k9_relat_1('#skF_13',D_409) ),
    inference(resolution,[status(thm)],[c_56,c_1996])).

tff(c_1598,plain,(
    ! [A_341,B_342,C_343,D_344] :
      ( k7_relset_1(A_341,B_342,C_343,D_344) = k9_relat_1(C_343,D_344)
      | ~ m1_subset_1(C_343,k1_zfmisc_1(k2_zfmisc_1(A_341,B_342))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1605,plain,(
    ! [D_344] : k7_relset_1('#skF_12','#skF_10','#skF_13',D_344) = k9_relat_1('#skF_13',D_344) ),
    inference(resolution,[status(thm)],[c_56,c_1598])).

tff(c_1223,plain,(
    ! [A_281,B_282,C_283,D_284] :
      ( k7_relset_1(A_281,B_282,C_283,D_284) = k9_relat_1(C_283,D_284)
      | ~ m1_subset_1(C_283,k1_zfmisc_1(k2_zfmisc_1(A_281,B_282))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1230,plain,(
    ! [D_284] : k7_relset_1('#skF_12','#skF_10','#skF_13',D_284) = k9_relat_1('#skF_13',D_284) ),
    inference(resolution,[status(thm)],[c_56,c_1223])).

tff(c_78,plain,
    ( r2_hidden('#skF_14',k7_relset_1('#skF_12','#skF_10','#skF_13','#skF_11'))
    | m1_subset_1('#skF_15','#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_88,plain,(
    m1_subset_1('#skF_15','#skF_12') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_70,plain,
    ( r2_hidden('#skF_14',k7_relset_1('#skF_12','#skF_10','#skF_13','#skF_11'))
    | r2_hidden('#skF_15','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_111,plain,(
    r2_hidden('#skF_15','#skF_11') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_74,plain,
    ( r2_hidden('#skF_14',k7_relset_1('#skF_12','#skF_10','#skF_13','#skF_11'))
    | r2_hidden(k4_tarski('#skF_15','#skF_14'),'#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_112,plain,(
    r2_hidden(k4_tarski('#skF_15','#skF_14'),'#skF_13') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_185,plain,(
    ! [A_184,B_185,C_186,D_187] :
      ( k7_relset_1(A_184,B_185,C_186,D_187) = k9_relat_1(C_186,D_187)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(A_184,B_185))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_192,plain,(
    ! [D_187] : k7_relset_1('#skF_12','#skF_10','#skF_13',D_187) = k9_relat_1('#skF_13',D_187) ),
    inference(resolution,[status(thm)],[c_56,c_185])).

tff(c_64,plain,(
    ! [F_149] :
      ( ~ r2_hidden(F_149,'#skF_11')
      | ~ r2_hidden(k4_tarski(F_149,'#skF_14'),'#skF_13')
      | ~ m1_subset_1(F_149,'#skF_12')
      | ~ r2_hidden('#skF_14',k7_relset_1('#skF_12','#skF_10','#skF_13','#skF_11')) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_342,plain,(
    ! [F_149] :
      ( ~ r2_hidden(F_149,'#skF_11')
      | ~ r2_hidden(k4_tarski(F_149,'#skF_14'),'#skF_13')
      | ~ m1_subset_1(F_149,'#skF_12')
      | ~ r2_hidden('#skF_14',k9_relat_1('#skF_13','#skF_11')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_64])).

tff(c_343,plain,(
    ~ r2_hidden('#skF_14',k9_relat_1('#skF_13','#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_342])).

tff(c_26,plain,(
    ! [C_40,A_25,D_43] :
      ( r2_hidden(C_40,k1_relat_1(A_25))
      | ~ r2_hidden(k4_tarski(C_40,D_43),A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_123,plain,(
    r2_hidden('#skF_15',k1_relat_1('#skF_13')) ),
    inference(resolution,[status(thm)],[c_112,c_26])).

tff(c_1060,plain,(
    ! [A_260,C_261,B_262,D_263] :
      ( r2_hidden(A_260,k9_relat_1(C_261,B_262))
      | ~ r2_hidden(D_263,B_262)
      | ~ r2_hidden(k4_tarski(D_263,A_260),C_261)
      | ~ r2_hidden(D_263,k1_relat_1(C_261))
      | ~ v1_relat_1(C_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1118,plain,(
    ! [A_264,C_265] :
      ( r2_hidden(A_264,k9_relat_1(C_265,'#skF_11'))
      | ~ r2_hidden(k4_tarski('#skF_15',A_264),C_265)
      | ~ r2_hidden('#skF_15',k1_relat_1(C_265))
      | ~ v1_relat_1(C_265) ) ),
    inference(resolution,[status(thm)],[c_111,c_1060])).

tff(c_1129,plain,
    ( r2_hidden('#skF_14',k9_relat_1('#skF_13','#skF_11'))
    | ~ r2_hidden('#skF_15',k1_relat_1('#skF_13'))
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_112,c_1118])).

tff(c_1134,plain,(
    r2_hidden('#skF_14',k9_relat_1('#skF_13','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_123,c_1129])).

tff(c_1136,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_343,c_1134])).

tff(c_1148,plain,(
    ! [F_266] :
      ( ~ r2_hidden(F_266,'#skF_11')
      | ~ r2_hidden(k4_tarski(F_266,'#skF_14'),'#skF_13')
      | ~ m1_subset_1(F_266,'#skF_12') ) ),
    inference(splitRight,[status(thm)],[c_342])).

tff(c_1155,plain,
    ( ~ r2_hidden('#skF_15','#skF_11')
    | ~ m1_subset_1('#skF_15','#skF_12') ),
    inference(resolution,[status(thm)],[c_112,c_1148])).

tff(c_1162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_111,c_1155])).

tff(c_1163,plain,(
    r2_hidden('#skF_14',k7_relset_1('#skF_12','#skF_10','#skF_13','#skF_11')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_1232,plain,(
    r2_hidden('#skF_14',k9_relat_1('#skF_13','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1230,c_1163])).

tff(c_42,plain,(
    ! [A_46,B_47,C_48] :
      ( r2_hidden(k4_tarski('#skF_9'(A_46,B_47,C_48),A_46),C_48)
      | ~ r2_hidden(A_46,k9_relat_1(C_48,B_47))
      | ~ v1_relat_1(C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_90,plain,(
    ! [C_159,A_160,B_161] :
      ( v4_relat_1(C_159,A_160)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_94,plain,(
    v4_relat_1('#skF_13','#skF_12') ),
    inference(resolution,[status(thm)],[c_56,c_90])).

tff(c_95,plain,(
    ! [B_162,A_163] :
      ( k7_relat_1(B_162,A_163) = B_162
      | ~ v4_relat_1(B_162,A_163)
      | ~ v1_relat_1(B_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_98,plain,
    ( k7_relat_1('#skF_13','#skF_12') = '#skF_13'
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_94,c_95])).

tff(c_101,plain,(
    k7_relat_1('#skF_13','#skF_12') = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_98])).

tff(c_1302,plain,(
    ! [D_302,B_303,E_304,A_305] :
      ( r2_hidden(D_302,B_303)
      | ~ r2_hidden(k4_tarski(D_302,E_304),k7_relat_1(A_305,B_303))
      | ~ v1_relat_1(k7_relat_1(A_305,B_303))
      | ~ v1_relat_1(A_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1313,plain,(
    ! [D_302,E_304] :
      ( r2_hidden(D_302,'#skF_12')
      | ~ r2_hidden(k4_tarski(D_302,E_304),'#skF_13')
      | ~ v1_relat_1(k7_relat_1('#skF_13','#skF_12'))
      | ~ v1_relat_1('#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_1302])).

tff(c_1336,plain,(
    ! [D_308,E_309] :
      ( r2_hidden(D_308,'#skF_12')
      | ~ r2_hidden(k4_tarski(D_308,E_309),'#skF_13') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_87,c_101,c_1313])).

tff(c_1344,plain,(
    ! [A_46,B_47] :
      ( r2_hidden('#skF_9'(A_46,B_47,'#skF_13'),'#skF_12')
      | ~ r2_hidden(A_46,k9_relat_1('#skF_13',B_47))
      | ~ v1_relat_1('#skF_13') ) ),
    inference(resolution,[status(thm)],[c_42,c_1336])).

tff(c_1387,plain,(
    ! [A_311,B_312] :
      ( r2_hidden('#skF_9'(A_311,B_312,'#skF_13'),'#skF_12')
      | ~ r2_hidden(A_311,k9_relat_1('#skF_13',B_312)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_1344])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1394,plain,(
    ! [A_313,B_314] :
      ( m1_subset_1('#skF_9'(A_313,B_314,'#skF_13'),'#skF_12')
      | ~ r2_hidden(A_313,k9_relat_1('#skF_13',B_314)) ) ),
    inference(resolution,[status(thm)],[c_1387,c_2])).

tff(c_1420,plain,(
    m1_subset_1('#skF_9'('#skF_14','#skF_11','#skF_13'),'#skF_12') ),
    inference(resolution,[status(thm)],[c_1232,c_1394])).

tff(c_40,plain,(
    ! [A_46,B_47,C_48] :
      ( r2_hidden('#skF_9'(A_46,B_47,C_48),B_47)
      | ~ r2_hidden(A_46,k9_relat_1(C_48,B_47))
      | ~ v1_relat_1(C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1261,plain,(
    ! [A_293,B_294,C_295] :
      ( r2_hidden(k4_tarski('#skF_9'(A_293,B_294,C_295),A_293),C_295)
      | ~ r2_hidden(A_293,k9_relat_1(C_295,B_294))
      | ~ v1_relat_1(C_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1164,plain,(
    ~ r2_hidden(k4_tarski('#skF_15','#skF_14'),'#skF_13') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_72,plain,(
    ! [F_149] :
      ( ~ r2_hidden(F_149,'#skF_11')
      | ~ r2_hidden(k4_tarski(F_149,'#skF_14'),'#skF_13')
      | ~ m1_subset_1(F_149,'#skF_12')
      | r2_hidden(k4_tarski('#skF_15','#skF_14'),'#skF_13') ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1258,plain,(
    ! [F_149] :
      ( ~ r2_hidden(F_149,'#skF_11')
      | ~ r2_hidden(k4_tarski(F_149,'#skF_14'),'#skF_13')
      | ~ m1_subset_1(F_149,'#skF_12') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1164,c_72])).

tff(c_1265,plain,(
    ! [B_294] :
      ( ~ r2_hidden('#skF_9'('#skF_14',B_294,'#skF_13'),'#skF_11')
      | ~ m1_subset_1('#skF_9'('#skF_14',B_294,'#skF_13'),'#skF_12')
      | ~ r2_hidden('#skF_14',k9_relat_1('#skF_13',B_294))
      | ~ v1_relat_1('#skF_13') ) ),
    inference(resolution,[status(thm)],[c_1261,c_1258])).

tff(c_1525,plain,(
    ! [B_322] :
      ( ~ r2_hidden('#skF_9'('#skF_14',B_322,'#skF_13'),'#skF_11')
      | ~ m1_subset_1('#skF_9'('#skF_14',B_322,'#skF_13'),'#skF_12')
      | ~ r2_hidden('#skF_14',k9_relat_1('#skF_13',B_322)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_1265])).

tff(c_1529,plain,
    ( ~ m1_subset_1('#skF_9'('#skF_14','#skF_11','#skF_13'),'#skF_12')
    | ~ r2_hidden('#skF_14',k9_relat_1('#skF_13','#skF_11'))
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_40,c_1525])).

tff(c_1533,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_1232,c_1420,c_1529])).

tff(c_1534,plain,(
    r2_hidden('#skF_14',k7_relset_1('#skF_12','#skF_10','#skF_13','#skF_11')) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_1607,plain,(
    r2_hidden('#skF_14',k9_relat_1('#skF_13','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1605,c_1534])).

tff(c_1669,plain,(
    ! [D_358,B_359,E_360,A_361] :
      ( r2_hidden(D_358,B_359)
      | ~ r2_hidden(k4_tarski(D_358,E_360),k7_relat_1(A_361,B_359))
      | ~ v1_relat_1(k7_relat_1(A_361,B_359))
      | ~ v1_relat_1(A_361) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1680,plain,(
    ! [D_358,E_360] :
      ( r2_hidden(D_358,'#skF_12')
      | ~ r2_hidden(k4_tarski(D_358,E_360),'#skF_13')
      | ~ v1_relat_1(k7_relat_1('#skF_13','#skF_12'))
      | ~ v1_relat_1('#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_1669])).

tff(c_1685,plain,(
    ! [D_362,E_363] :
      ( r2_hidden(D_362,'#skF_12')
      | ~ r2_hidden(k4_tarski(D_362,E_363),'#skF_13') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_87,c_101,c_1680])).

tff(c_1689,plain,(
    ! [A_46,B_47] :
      ( r2_hidden('#skF_9'(A_46,B_47,'#skF_13'),'#skF_12')
      | ~ r2_hidden(A_46,k9_relat_1('#skF_13',B_47))
      | ~ v1_relat_1('#skF_13') ) ),
    inference(resolution,[status(thm)],[c_42,c_1685])).

tff(c_1754,plain,(
    ! [A_367,B_368] :
      ( r2_hidden('#skF_9'(A_367,B_368,'#skF_13'),'#skF_12')
      | ~ r2_hidden(A_367,k9_relat_1('#skF_13',B_368)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_1689])).

tff(c_1761,plain,(
    ! [A_369,B_370] :
      ( m1_subset_1('#skF_9'(A_369,B_370,'#skF_13'),'#skF_12')
      | ~ r2_hidden(A_369,k9_relat_1('#skF_13',B_370)) ) ),
    inference(resolution,[status(thm)],[c_1754,c_2])).

tff(c_1786,plain,(
    m1_subset_1('#skF_9'('#skF_14','#skF_11','#skF_13'),'#skF_12') ),
    inference(resolution,[status(thm)],[c_1607,c_1761])).

tff(c_1617,plain,(
    ! [A_346,B_347,C_348] :
      ( r2_hidden(k4_tarski('#skF_9'(A_346,B_347,C_348),A_346),C_348)
      | ~ r2_hidden(A_346,k9_relat_1(C_348,B_347))
      | ~ v1_relat_1(C_348) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1535,plain,(
    ~ r2_hidden('#skF_15','#skF_11') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_68,plain,(
    ! [F_149] :
      ( ~ r2_hidden(F_149,'#skF_11')
      | ~ r2_hidden(k4_tarski(F_149,'#skF_14'),'#skF_13')
      | ~ m1_subset_1(F_149,'#skF_12')
      | r2_hidden('#skF_15','#skF_11') ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1574,plain,(
    ! [F_149] :
      ( ~ r2_hidden(F_149,'#skF_11')
      | ~ r2_hidden(k4_tarski(F_149,'#skF_14'),'#skF_13')
      | ~ m1_subset_1(F_149,'#skF_12') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1535,c_68])).

tff(c_1621,plain,(
    ! [B_347] :
      ( ~ r2_hidden('#skF_9'('#skF_14',B_347,'#skF_13'),'#skF_11')
      | ~ m1_subset_1('#skF_9'('#skF_14',B_347,'#skF_13'),'#skF_12')
      | ~ r2_hidden('#skF_14',k9_relat_1('#skF_13',B_347))
      | ~ v1_relat_1('#skF_13') ) ),
    inference(resolution,[status(thm)],[c_1617,c_1574])).

tff(c_1906,plain,(
    ! [B_379] :
      ( ~ r2_hidden('#skF_9'('#skF_14',B_379,'#skF_13'),'#skF_11')
      | ~ m1_subset_1('#skF_9'('#skF_14',B_379,'#skF_13'),'#skF_12')
      | ~ r2_hidden('#skF_14',k9_relat_1('#skF_13',B_379)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_1621])).

tff(c_1910,plain,
    ( ~ m1_subset_1('#skF_9'('#skF_14','#skF_11','#skF_13'),'#skF_12')
    | ~ r2_hidden('#skF_14',k9_relat_1('#skF_13','#skF_11'))
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_40,c_1906])).

tff(c_1914,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_1607,c_1786,c_1910])).

tff(c_1915,plain,(
    r2_hidden('#skF_14',k7_relset_1('#skF_12','#skF_10','#skF_13','#skF_11')) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_2005,plain,(
    r2_hidden('#skF_14',k9_relat_1('#skF_13','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2003,c_1915])).

tff(c_1921,plain,(
    ! [C_380,A_381,B_382] :
      ( v4_relat_1(C_380,A_381)
      | ~ m1_subset_1(C_380,k1_zfmisc_1(k2_zfmisc_1(A_381,B_382))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1925,plain,(
    v4_relat_1('#skF_13','#skF_12') ),
    inference(resolution,[status(thm)],[c_56,c_1921])).

tff(c_1931,plain,(
    ! [B_386,A_387] :
      ( k7_relat_1(B_386,A_387) = B_386
      | ~ v4_relat_1(B_386,A_387)
      | ~ v1_relat_1(B_386) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1934,plain,
    ( k7_relat_1('#skF_13','#skF_12') = '#skF_13'
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_1925,c_1931])).

tff(c_1937,plain,(
    k7_relat_1('#skF_13','#skF_12') = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_1934])).

tff(c_2072,plain,(
    ! [D_426,B_427,E_428,A_429] :
      ( r2_hidden(D_426,B_427)
      | ~ r2_hidden(k4_tarski(D_426,E_428),k7_relat_1(A_429,B_427))
      | ~ v1_relat_1(k7_relat_1(A_429,B_427))
      | ~ v1_relat_1(A_429) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2083,plain,(
    ! [D_426,E_428] :
      ( r2_hidden(D_426,'#skF_12')
      | ~ r2_hidden(k4_tarski(D_426,E_428),'#skF_13')
      | ~ v1_relat_1(k7_relat_1('#skF_13','#skF_12'))
      | ~ v1_relat_1('#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1937,c_2072])).

tff(c_2088,plain,(
    ! [D_430,E_431] :
      ( r2_hidden(D_430,'#skF_12')
      | ~ r2_hidden(k4_tarski(D_430,E_431),'#skF_13') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_87,c_1937,c_2083])).

tff(c_2092,plain,(
    ! [A_46,B_47] :
      ( r2_hidden('#skF_9'(A_46,B_47,'#skF_13'),'#skF_12')
      | ~ r2_hidden(A_46,k9_relat_1('#skF_13',B_47))
      | ~ v1_relat_1('#skF_13') ) ),
    inference(resolution,[status(thm)],[c_42,c_2088])).

tff(c_2129,plain,(
    ! [A_433,B_434] :
      ( r2_hidden('#skF_9'(A_433,B_434,'#skF_13'),'#skF_12')
      | ~ r2_hidden(A_433,k9_relat_1('#skF_13',B_434)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_2092])).

tff(c_2162,plain,(
    ! [A_437,B_438] :
      ( m1_subset_1('#skF_9'(A_437,B_438,'#skF_13'),'#skF_12')
      | ~ r2_hidden(A_437,k9_relat_1('#skF_13',B_438)) ) ),
    inference(resolution,[status(thm)],[c_2129,c_2])).

tff(c_2188,plain,(
    m1_subset_1('#skF_9'('#skF_14','#skF_11','#skF_13'),'#skF_12') ),
    inference(resolution,[status(thm)],[c_2005,c_2162])).

tff(c_2031,plain,(
    ! [A_417,B_418,C_419] :
      ( r2_hidden(k4_tarski('#skF_9'(A_417,B_418,C_419),A_417),C_419)
      | ~ r2_hidden(A_417,k9_relat_1(C_419,B_418))
      | ~ v1_relat_1(C_419) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1916,plain,(
    ~ m1_subset_1('#skF_15','#skF_12') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_76,plain,(
    ! [F_149] :
      ( ~ r2_hidden(F_149,'#skF_11')
      | ~ r2_hidden(k4_tarski(F_149,'#skF_14'),'#skF_13')
      | ~ m1_subset_1(F_149,'#skF_12')
      | m1_subset_1('#skF_15','#skF_12') ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1964,plain,(
    ! [F_149] :
      ( ~ r2_hidden(F_149,'#skF_11')
      | ~ r2_hidden(k4_tarski(F_149,'#skF_14'),'#skF_13')
      | ~ m1_subset_1(F_149,'#skF_12') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1916,c_76])).

tff(c_2038,plain,(
    ! [B_418] :
      ( ~ r2_hidden('#skF_9'('#skF_14',B_418,'#skF_13'),'#skF_11')
      | ~ m1_subset_1('#skF_9'('#skF_14',B_418,'#skF_13'),'#skF_12')
      | ~ r2_hidden('#skF_14',k9_relat_1('#skF_13',B_418))
      | ~ v1_relat_1('#skF_13') ) ),
    inference(resolution,[status(thm)],[c_2031,c_1964])).

tff(c_2360,plain,(
    ! [B_449] :
      ( ~ r2_hidden('#skF_9'('#skF_14',B_449,'#skF_13'),'#skF_11')
      | ~ m1_subset_1('#skF_9'('#skF_14',B_449,'#skF_13'),'#skF_12')
      | ~ r2_hidden('#skF_14',k9_relat_1('#skF_13',B_449)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_2038])).

tff(c_2364,plain,
    ( ~ m1_subset_1('#skF_9'('#skF_14','#skF_11','#skF_13'),'#skF_12')
    | ~ r2_hidden('#skF_14',k9_relat_1('#skF_13','#skF_11'))
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_40,c_2360])).

tff(c_2368,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_2005,c_2188,c_2364])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n005.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 18:26:32 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.41/1.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.41/1.76  
% 4.41/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.41/1.76  %$ v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_relset_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_6 > #skF_1 > #skF_11 > #skF_15 > #skF_4 > #skF_10 > #skF_14 > #skF_13 > #skF_2 > #skF_9 > #skF_3 > #skF_8 > #skF_7 > #skF_5 > #skF_12
% 4.41/1.76  
% 4.41/1.76  %Foreground sorts:
% 4.41/1.76  
% 4.41/1.76  
% 4.41/1.76  %Background operators:
% 4.41/1.76  
% 4.41/1.76  
% 4.41/1.76  %Foreground operators:
% 4.41/1.76  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.41/1.76  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.41/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.41/1.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.41/1.76  tff('#skF_11', type, '#skF_11': $i).
% 4.41/1.76  tff('#skF_15', type, '#skF_15': $i).
% 4.41/1.76  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.41/1.76  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.41/1.76  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.41/1.76  tff('#skF_10', type, '#skF_10': $i).
% 4.41/1.76  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.41/1.76  tff('#skF_14', type, '#skF_14': $i).
% 4.41/1.76  tff('#skF_13', type, '#skF_13': $i).
% 4.41/1.76  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.41/1.76  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.41/1.76  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.41/1.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.41/1.76  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 4.41/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.41/1.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.41/1.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.41/1.76  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.41/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.41/1.76  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.41/1.76  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 4.41/1.76  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 4.41/1.76  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.41/1.76  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.41/1.76  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.41/1.76  tff('#skF_12', type, '#skF_12': $i).
% 4.41/1.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.41/1.76  
% 4.48/1.80  tff(f_60, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.48/1.80  tff(f_114, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k7_relset_1(C, A, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(F, E), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relset_1)).
% 4.48/1.80  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.48/1.80  tff(f_87, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.48/1.80  tff(f_58, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 4.48/1.80  tff(f_71, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 4.48/1.80  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.48/1.80  tff(f_77, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 4.48/1.80  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (v1_relat_1(C) => ((C = k7_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (r2_hidden(D, B) & r2_hidden(k4_tarski(D, E), A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_relat_1)).
% 4.48/1.80  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 4.48/1.80  tff(c_36, plain, (![A_44, B_45]: (v1_relat_1(k2_zfmisc_1(A_44, B_45)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.48/1.80  tff(c_56, plain, (m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1('#skF_12', '#skF_10')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.48/1.80  tff(c_81, plain, (![B_154, A_155]: (v1_relat_1(B_154) | ~m1_subset_1(B_154, k1_zfmisc_1(A_155)) | ~v1_relat_1(A_155))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.48/1.80  tff(c_84, plain, (v1_relat_1('#skF_13') | ~v1_relat_1(k2_zfmisc_1('#skF_12', '#skF_10'))), inference(resolution, [status(thm)], [c_56, c_81])).
% 4.48/1.80  tff(c_87, plain, (v1_relat_1('#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_84])).
% 4.48/1.80  tff(c_1996, plain, (![A_406, B_407, C_408, D_409]: (k7_relset_1(A_406, B_407, C_408, D_409)=k9_relat_1(C_408, D_409) | ~m1_subset_1(C_408, k1_zfmisc_1(k2_zfmisc_1(A_406, B_407))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.48/1.80  tff(c_2003, plain, (![D_409]: (k7_relset_1('#skF_12', '#skF_10', '#skF_13', D_409)=k9_relat_1('#skF_13', D_409))), inference(resolution, [status(thm)], [c_56, c_1996])).
% 4.48/1.80  tff(c_1598, plain, (![A_341, B_342, C_343, D_344]: (k7_relset_1(A_341, B_342, C_343, D_344)=k9_relat_1(C_343, D_344) | ~m1_subset_1(C_343, k1_zfmisc_1(k2_zfmisc_1(A_341, B_342))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.48/1.80  tff(c_1605, plain, (![D_344]: (k7_relset_1('#skF_12', '#skF_10', '#skF_13', D_344)=k9_relat_1('#skF_13', D_344))), inference(resolution, [status(thm)], [c_56, c_1598])).
% 4.48/1.80  tff(c_1223, plain, (![A_281, B_282, C_283, D_284]: (k7_relset_1(A_281, B_282, C_283, D_284)=k9_relat_1(C_283, D_284) | ~m1_subset_1(C_283, k1_zfmisc_1(k2_zfmisc_1(A_281, B_282))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.48/1.80  tff(c_1230, plain, (![D_284]: (k7_relset_1('#skF_12', '#skF_10', '#skF_13', D_284)=k9_relat_1('#skF_13', D_284))), inference(resolution, [status(thm)], [c_56, c_1223])).
% 4.48/1.80  tff(c_78, plain, (r2_hidden('#skF_14', k7_relset_1('#skF_12', '#skF_10', '#skF_13', '#skF_11')) | m1_subset_1('#skF_15', '#skF_12')), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.48/1.80  tff(c_88, plain, (m1_subset_1('#skF_15', '#skF_12')), inference(splitLeft, [status(thm)], [c_78])).
% 4.48/1.80  tff(c_70, plain, (r2_hidden('#skF_14', k7_relset_1('#skF_12', '#skF_10', '#skF_13', '#skF_11')) | r2_hidden('#skF_15', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.48/1.80  tff(c_111, plain, (r2_hidden('#skF_15', '#skF_11')), inference(splitLeft, [status(thm)], [c_70])).
% 4.48/1.80  tff(c_74, plain, (r2_hidden('#skF_14', k7_relset_1('#skF_12', '#skF_10', '#skF_13', '#skF_11')) | r2_hidden(k4_tarski('#skF_15', '#skF_14'), '#skF_13')), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.48/1.80  tff(c_112, plain, (r2_hidden(k4_tarski('#skF_15', '#skF_14'), '#skF_13')), inference(splitLeft, [status(thm)], [c_74])).
% 4.48/1.80  tff(c_185, plain, (![A_184, B_185, C_186, D_187]: (k7_relset_1(A_184, B_185, C_186, D_187)=k9_relat_1(C_186, D_187) | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(A_184, B_185))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.48/1.80  tff(c_192, plain, (![D_187]: (k7_relset_1('#skF_12', '#skF_10', '#skF_13', D_187)=k9_relat_1('#skF_13', D_187))), inference(resolution, [status(thm)], [c_56, c_185])).
% 4.48/1.80  tff(c_64, plain, (![F_149]: (~r2_hidden(F_149, '#skF_11') | ~r2_hidden(k4_tarski(F_149, '#skF_14'), '#skF_13') | ~m1_subset_1(F_149, '#skF_12') | ~r2_hidden('#skF_14', k7_relset_1('#skF_12', '#skF_10', '#skF_13', '#skF_11')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.48/1.80  tff(c_342, plain, (![F_149]: (~r2_hidden(F_149, '#skF_11') | ~r2_hidden(k4_tarski(F_149, '#skF_14'), '#skF_13') | ~m1_subset_1(F_149, '#skF_12') | ~r2_hidden('#skF_14', k9_relat_1('#skF_13', '#skF_11')))), inference(demodulation, [status(thm), theory('equality')], [c_192, c_64])).
% 4.48/1.80  tff(c_343, plain, (~r2_hidden('#skF_14', k9_relat_1('#skF_13', '#skF_11'))), inference(splitLeft, [status(thm)], [c_342])).
% 4.48/1.80  tff(c_26, plain, (![C_40, A_25, D_43]: (r2_hidden(C_40, k1_relat_1(A_25)) | ~r2_hidden(k4_tarski(C_40, D_43), A_25))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.48/1.80  tff(c_123, plain, (r2_hidden('#skF_15', k1_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_112, c_26])).
% 4.48/1.80  tff(c_1060, plain, (![A_260, C_261, B_262, D_263]: (r2_hidden(A_260, k9_relat_1(C_261, B_262)) | ~r2_hidden(D_263, B_262) | ~r2_hidden(k4_tarski(D_263, A_260), C_261) | ~r2_hidden(D_263, k1_relat_1(C_261)) | ~v1_relat_1(C_261))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.48/1.80  tff(c_1118, plain, (![A_264, C_265]: (r2_hidden(A_264, k9_relat_1(C_265, '#skF_11')) | ~r2_hidden(k4_tarski('#skF_15', A_264), C_265) | ~r2_hidden('#skF_15', k1_relat_1(C_265)) | ~v1_relat_1(C_265))), inference(resolution, [status(thm)], [c_111, c_1060])).
% 4.48/1.80  tff(c_1129, plain, (r2_hidden('#skF_14', k9_relat_1('#skF_13', '#skF_11')) | ~r2_hidden('#skF_15', k1_relat_1('#skF_13')) | ~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_112, c_1118])).
% 4.48/1.80  tff(c_1134, plain, (r2_hidden('#skF_14', k9_relat_1('#skF_13', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_123, c_1129])).
% 4.48/1.80  tff(c_1136, plain, $false, inference(negUnitSimplification, [status(thm)], [c_343, c_1134])).
% 4.48/1.80  tff(c_1148, plain, (![F_266]: (~r2_hidden(F_266, '#skF_11') | ~r2_hidden(k4_tarski(F_266, '#skF_14'), '#skF_13') | ~m1_subset_1(F_266, '#skF_12'))), inference(splitRight, [status(thm)], [c_342])).
% 4.48/1.80  tff(c_1155, plain, (~r2_hidden('#skF_15', '#skF_11') | ~m1_subset_1('#skF_15', '#skF_12')), inference(resolution, [status(thm)], [c_112, c_1148])).
% 4.48/1.80  tff(c_1162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_111, c_1155])).
% 4.48/1.80  tff(c_1163, plain, (r2_hidden('#skF_14', k7_relset_1('#skF_12', '#skF_10', '#skF_13', '#skF_11'))), inference(splitRight, [status(thm)], [c_74])).
% 4.48/1.80  tff(c_1232, plain, (r2_hidden('#skF_14', k9_relat_1('#skF_13', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_1230, c_1163])).
% 4.48/1.80  tff(c_42, plain, (![A_46, B_47, C_48]: (r2_hidden(k4_tarski('#skF_9'(A_46, B_47, C_48), A_46), C_48) | ~r2_hidden(A_46, k9_relat_1(C_48, B_47)) | ~v1_relat_1(C_48))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.48/1.80  tff(c_90, plain, (![C_159, A_160, B_161]: (v4_relat_1(C_159, A_160) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.48/1.80  tff(c_94, plain, (v4_relat_1('#skF_13', '#skF_12')), inference(resolution, [status(thm)], [c_56, c_90])).
% 4.48/1.80  tff(c_95, plain, (![B_162, A_163]: (k7_relat_1(B_162, A_163)=B_162 | ~v4_relat_1(B_162, A_163) | ~v1_relat_1(B_162))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.48/1.80  tff(c_98, plain, (k7_relat_1('#skF_13', '#skF_12')='#skF_13' | ~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_94, c_95])).
% 4.48/1.80  tff(c_101, plain, (k7_relat_1('#skF_13', '#skF_12')='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_87, c_98])).
% 4.48/1.80  tff(c_1302, plain, (![D_302, B_303, E_304, A_305]: (r2_hidden(D_302, B_303) | ~r2_hidden(k4_tarski(D_302, E_304), k7_relat_1(A_305, B_303)) | ~v1_relat_1(k7_relat_1(A_305, B_303)) | ~v1_relat_1(A_305))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.48/1.80  tff(c_1313, plain, (![D_302, E_304]: (r2_hidden(D_302, '#skF_12') | ~r2_hidden(k4_tarski(D_302, E_304), '#skF_13') | ~v1_relat_1(k7_relat_1('#skF_13', '#skF_12')) | ~v1_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_1302])).
% 4.48/1.80  tff(c_1336, plain, (![D_308, E_309]: (r2_hidden(D_308, '#skF_12') | ~r2_hidden(k4_tarski(D_308, E_309), '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_87, c_101, c_1313])).
% 4.48/1.80  tff(c_1344, plain, (![A_46, B_47]: (r2_hidden('#skF_9'(A_46, B_47, '#skF_13'), '#skF_12') | ~r2_hidden(A_46, k9_relat_1('#skF_13', B_47)) | ~v1_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_42, c_1336])).
% 4.48/1.80  tff(c_1387, plain, (![A_311, B_312]: (r2_hidden('#skF_9'(A_311, B_312, '#skF_13'), '#skF_12') | ~r2_hidden(A_311, k9_relat_1('#skF_13', B_312)))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_1344])).
% 4.48/1.80  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.48/1.80  tff(c_1394, plain, (![A_313, B_314]: (m1_subset_1('#skF_9'(A_313, B_314, '#skF_13'), '#skF_12') | ~r2_hidden(A_313, k9_relat_1('#skF_13', B_314)))), inference(resolution, [status(thm)], [c_1387, c_2])).
% 4.48/1.80  tff(c_1420, plain, (m1_subset_1('#skF_9'('#skF_14', '#skF_11', '#skF_13'), '#skF_12')), inference(resolution, [status(thm)], [c_1232, c_1394])).
% 4.48/1.80  tff(c_40, plain, (![A_46, B_47, C_48]: (r2_hidden('#skF_9'(A_46, B_47, C_48), B_47) | ~r2_hidden(A_46, k9_relat_1(C_48, B_47)) | ~v1_relat_1(C_48))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.48/1.80  tff(c_1261, plain, (![A_293, B_294, C_295]: (r2_hidden(k4_tarski('#skF_9'(A_293, B_294, C_295), A_293), C_295) | ~r2_hidden(A_293, k9_relat_1(C_295, B_294)) | ~v1_relat_1(C_295))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.48/1.80  tff(c_1164, plain, (~r2_hidden(k4_tarski('#skF_15', '#skF_14'), '#skF_13')), inference(splitRight, [status(thm)], [c_74])).
% 4.48/1.80  tff(c_72, plain, (![F_149]: (~r2_hidden(F_149, '#skF_11') | ~r2_hidden(k4_tarski(F_149, '#skF_14'), '#skF_13') | ~m1_subset_1(F_149, '#skF_12') | r2_hidden(k4_tarski('#skF_15', '#skF_14'), '#skF_13'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.48/1.80  tff(c_1258, plain, (![F_149]: (~r2_hidden(F_149, '#skF_11') | ~r2_hidden(k4_tarski(F_149, '#skF_14'), '#skF_13') | ~m1_subset_1(F_149, '#skF_12'))), inference(negUnitSimplification, [status(thm)], [c_1164, c_72])).
% 4.48/1.80  tff(c_1265, plain, (![B_294]: (~r2_hidden('#skF_9'('#skF_14', B_294, '#skF_13'), '#skF_11') | ~m1_subset_1('#skF_9'('#skF_14', B_294, '#skF_13'), '#skF_12') | ~r2_hidden('#skF_14', k9_relat_1('#skF_13', B_294)) | ~v1_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_1261, c_1258])).
% 4.48/1.80  tff(c_1525, plain, (![B_322]: (~r2_hidden('#skF_9'('#skF_14', B_322, '#skF_13'), '#skF_11') | ~m1_subset_1('#skF_9'('#skF_14', B_322, '#skF_13'), '#skF_12') | ~r2_hidden('#skF_14', k9_relat_1('#skF_13', B_322)))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_1265])).
% 4.48/1.80  tff(c_1529, plain, (~m1_subset_1('#skF_9'('#skF_14', '#skF_11', '#skF_13'), '#skF_12') | ~r2_hidden('#skF_14', k9_relat_1('#skF_13', '#skF_11')) | ~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_40, c_1525])).
% 4.48/1.80  tff(c_1533, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_1232, c_1420, c_1529])).
% 4.48/1.80  tff(c_1534, plain, (r2_hidden('#skF_14', k7_relset_1('#skF_12', '#skF_10', '#skF_13', '#skF_11'))), inference(splitRight, [status(thm)], [c_70])).
% 4.48/1.80  tff(c_1607, plain, (r2_hidden('#skF_14', k9_relat_1('#skF_13', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_1605, c_1534])).
% 4.48/1.80  tff(c_1669, plain, (![D_358, B_359, E_360, A_361]: (r2_hidden(D_358, B_359) | ~r2_hidden(k4_tarski(D_358, E_360), k7_relat_1(A_361, B_359)) | ~v1_relat_1(k7_relat_1(A_361, B_359)) | ~v1_relat_1(A_361))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.48/1.80  tff(c_1680, plain, (![D_358, E_360]: (r2_hidden(D_358, '#skF_12') | ~r2_hidden(k4_tarski(D_358, E_360), '#skF_13') | ~v1_relat_1(k7_relat_1('#skF_13', '#skF_12')) | ~v1_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_1669])).
% 4.48/1.80  tff(c_1685, plain, (![D_362, E_363]: (r2_hidden(D_362, '#skF_12') | ~r2_hidden(k4_tarski(D_362, E_363), '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_87, c_101, c_1680])).
% 4.48/1.80  tff(c_1689, plain, (![A_46, B_47]: (r2_hidden('#skF_9'(A_46, B_47, '#skF_13'), '#skF_12') | ~r2_hidden(A_46, k9_relat_1('#skF_13', B_47)) | ~v1_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_42, c_1685])).
% 4.48/1.80  tff(c_1754, plain, (![A_367, B_368]: (r2_hidden('#skF_9'(A_367, B_368, '#skF_13'), '#skF_12') | ~r2_hidden(A_367, k9_relat_1('#skF_13', B_368)))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_1689])).
% 4.48/1.80  tff(c_1761, plain, (![A_369, B_370]: (m1_subset_1('#skF_9'(A_369, B_370, '#skF_13'), '#skF_12') | ~r2_hidden(A_369, k9_relat_1('#skF_13', B_370)))), inference(resolution, [status(thm)], [c_1754, c_2])).
% 4.48/1.80  tff(c_1786, plain, (m1_subset_1('#skF_9'('#skF_14', '#skF_11', '#skF_13'), '#skF_12')), inference(resolution, [status(thm)], [c_1607, c_1761])).
% 4.48/1.80  tff(c_1617, plain, (![A_346, B_347, C_348]: (r2_hidden(k4_tarski('#skF_9'(A_346, B_347, C_348), A_346), C_348) | ~r2_hidden(A_346, k9_relat_1(C_348, B_347)) | ~v1_relat_1(C_348))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.48/1.80  tff(c_1535, plain, (~r2_hidden('#skF_15', '#skF_11')), inference(splitRight, [status(thm)], [c_70])).
% 4.48/1.80  tff(c_68, plain, (![F_149]: (~r2_hidden(F_149, '#skF_11') | ~r2_hidden(k4_tarski(F_149, '#skF_14'), '#skF_13') | ~m1_subset_1(F_149, '#skF_12') | r2_hidden('#skF_15', '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.48/1.80  tff(c_1574, plain, (![F_149]: (~r2_hidden(F_149, '#skF_11') | ~r2_hidden(k4_tarski(F_149, '#skF_14'), '#skF_13') | ~m1_subset_1(F_149, '#skF_12'))), inference(negUnitSimplification, [status(thm)], [c_1535, c_68])).
% 4.48/1.80  tff(c_1621, plain, (![B_347]: (~r2_hidden('#skF_9'('#skF_14', B_347, '#skF_13'), '#skF_11') | ~m1_subset_1('#skF_9'('#skF_14', B_347, '#skF_13'), '#skF_12') | ~r2_hidden('#skF_14', k9_relat_1('#skF_13', B_347)) | ~v1_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_1617, c_1574])).
% 4.48/1.80  tff(c_1906, plain, (![B_379]: (~r2_hidden('#skF_9'('#skF_14', B_379, '#skF_13'), '#skF_11') | ~m1_subset_1('#skF_9'('#skF_14', B_379, '#skF_13'), '#skF_12') | ~r2_hidden('#skF_14', k9_relat_1('#skF_13', B_379)))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_1621])).
% 4.48/1.80  tff(c_1910, plain, (~m1_subset_1('#skF_9'('#skF_14', '#skF_11', '#skF_13'), '#skF_12') | ~r2_hidden('#skF_14', k9_relat_1('#skF_13', '#skF_11')) | ~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_40, c_1906])).
% 4.48/1.80  tff(c_1914, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_1607, c_1786, c_1910])).
% 4.48/1.80  tff(c_1915, plain, (r2_hidden('#skF_14', k7_relset_1('#skF_12', '#skF_10', '#skF_13', '#skF_11'))), inference(splitRight, [status(thm)], [c_78])).
% 4.48/1.80  tff(c_2005, plain, (r2_hidden('#skF_14', k9_relat_1('#skF_13', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_2003, c_1915])).
% 4.48/1.80  tff(c_1921, plain, (![C_380, A_381, B_382]: (v4_relat_1(C_380, A_381) | ~m1_subset_1(C_380, k1_zfmisc_1(k2_zfmisc_1(A_381, B_382))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.48/1.80  tff(c_1925, plain, (v4_relat_1('#skF_13', '#skF_12')), inference(resolution, [status(thm)], [c_56, c_1921])).
% 4.48/1.80  tff(c_1931, plain, (![B_386, A_387]: (k7_relat_1(B_386, A_387)=B_386 | ~v4_relat_1(B_386, A_387) | ~v1_relat_1(B_386))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.48/1.80  tff(c_1934, plain, (k7_relat_1('#skF_13', '#skF_12')='#skF_13' | ~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_1925, c_1931])).
% 4.48/1.80  tff(c_1937, plain, (k7_relat_1('#skF_13', '#skF_12')='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_87, c_1934])).
% 4.48/1.80  tff(c_2072, plain, (![D_426, B_427, E_428, A_429]: (r2_hidden(D_426, B_427) | ~r2_hidden(k4_tarski(D_426, E_428), k7_relat_1(A_429, B_427)) | ~v1_relat_1(k7_relat_1(A_429, B_427)) | ~v1_relat_1(A_429))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.48/1.80  tff(c_2083, plain, (![D_426, E_428]: (r2_hidden(D_426, '#skF_12') | ~r2_hidden(k4_tarski(D_426, E_428), '#skF_13') | ~v1_relat_1(k7_relat_1('#skF_13', '#skF_12')) | ~v1_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_1937, c_2072])).
% 4.48/1.80  tff(c_2088, plain, (![D_430, E_431]: (r2_hidden(D_430, '#skF_12') | ~r2_hidden(k4_tarski(D_430, E_431), '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_87, c_1937, c_2083])).
% 4.48/1.80  tff(c_2092, plain, (![A_46, B_47]: (r2_hidden('#skF_9'(A_46, B_47, '#skF_13'), '#skF_12') | ~r2_hidden(A_46, k9_relat_1('#skF_13', B_47)) | ~v1_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_42, c_2088])).
% 4.48/1.80  tff(c_2129, plain, (![A_433, B_434]: (r2_hidden('#skF_9'(A_433, B_434, '#skF_13'), '#skF_12') | ~r2_hidden(A_433, k9_relat_1('#skF_13', B_434)))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_2092])).
% 4.48/1.80  tff(c_2162, plain, (![A_437, B_438]: (m1_subset_1('#skF_9'(A_437, B_438, '#skF_13'), '#skF_12') | ~r2_hidden(A_437, k9_relat_1('#skF_13', B_438)))), inference(resolution, [status(thm)], [c_2129, c_2])).
% 4.48/1.80  tff(c_2188, plain, (m1_subset_1('#skF_9'('#skF_14', '#skF_11', '#skF_13'), '#skF_12')), inference(resolution, [status(thm)], [c_2005, c_2162])).
% 4.48/1.80  tff(c_2031, plain, (![A_417, B_418, C_419]: (r2_hidden(k4_tarski('#skF_9'(A_417, B_418, C_419), A_417), C_419) | ~r2_hidden(A_417, k9_relat_1(C_419, B_418)) | ~v1_relat_1(C_419))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.48/1.80  tff(c_1916, plain, (~m1_subset_1('#skF_15', '#skF_12')), inference(splitRight, [status(thm)], [c_78])).
% 4.48/1.80  tff(c_76, plain, (![F_149]: (~r2_hidden(F_149, '#skF_11') | ~r2_hidden(k4_tarski(F_149, '#skF_14'), '#skF_13') | ~m1_subset_1(F_149, '#skF_12') | m1_subset_1('#skF_15', '#skF_12'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.48/1.80  tff(c_1964, plain, (![F_149]: (~r2_hidden(F_149, '#skF_11') | ~r2_hidden(k4_tarski(F_149, '#skF_14'), '#skF_13') | ~m1_subset_1(F_149, '#skF_12'))), inference(negUnitSimplification, [status(thm)], [c_1916, c_76])).
% 4.48/1.80  tff(c_2038, plain, (![B_418]: (~r2_hidden('#skF_9'('#skF_14', B_418, '#skF_13'), '#skF_11') | ~m1_subset_1('#skF_9'('#skF_14', B_418, '#skF_13'), '#skF_12') | ~r2_hidden('#skF_14', k9_relat_1('#skF_13', B_418)) | ~v1_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_2031, c_1964])).
% 4.48/1.80  tff(c_2360, plain, (![B_449]: (~r2_hidden('#skF_9'('#skF_14', B_449, '#skF_13'), '#skF_11') | ~m1_subset_1('#skF_9'('#skF_14', B_449, '#skF_13'), '#skF_12') | ~r2_hidden('#skF_14', k9_relat_1('#skF_13', B_449)))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_2038])).
% 4.48/1.80  tff(c_2364, plain, (~m1_subset_1('#skF_9'('#skF_14', '#skF_11', '#skF_13'), '#skF_12') | ~r2_hidden('#skF_14', k9_relat_1('#skF_13', '#skF_11')) | ~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_40, c_2360])).
% 4.48/1.80  tff(c_2368, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_2005, c_2188, c_2364])).
% 4.48/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.48/1.80  
% 4.48/1.80  Inference rules
% 4.48/1.80  ----------------------
% 4.48/1.80  #Ref     : 0
% 4.48/1.80  #Sup     : 461
% 4.48/1.80  #Fact    : 0
% 4.48/1.80  #Define  : 0
% 4.48/1.80  #Split   : 8
% 4.48/1.80  #Chain   : 0
% 4.48/1.80  #Close   : 0
% 4.48/1.80  
% 4.48/1.80  Ordering : KBO
% 4.48/1.80  
% 4.48/1.80  Simplification rules
% 4.48/1.80  ----------------------
% 4.48/1.80  #Subsume      : 36
% 4.48/1.80  #Demod        : 140
% 4.48/1.80  #Tautology    : 68
% 4.48/1.80  #SimpNegUnit  : 6
% 4.48/1.80  #BackRed      : 16
% 4.48/1.80  
% 4.48/1.80  #Partial instantiations: 0
% 4.48/1.80  #Strategies tried      : 1
% 4.48/1.80  
% 4.48/1.80  Timing (in seconds)
% 4.48/1.80  ----------------------
% 4.48/1.81  Preprocessing        : 0.35
% 4.48/1.81  Parsing              : 0.17
% 4.48/1.81  CNF conversion       : 0.04
% 4.48/1.81  Main loop            : 0.67
% 4.48/1.81  Inferencing          : 0.25
% 4.48/1.81  Reduction            : 0.19
% 4.48/1.81  Demodulation         : 0.13
% 4.48/1.81  BG Simplification    : 0.04
% 4.48/1.81  Subsumption          : 0.13
% 4.48/1.81  Abstraction          : 0.04
% 4.48/1.81  MUC search           : 0.00
% 4.48/1.81  Cooper               : 0.00
% 4.48/1.81  Total                : 1.09
% 4.48/1.81  Index Insertion      : 0.00
% 4.48/1.81  Index Deletion       : 0.00
% 4.48/1.81  Index Matching       : 0.00
% 4.48/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
